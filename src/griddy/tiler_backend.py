from general import *
import compiler2
import sft
from configuration import *
from automatic_conf import *
from enum import Enum

class AxisState(Enum):
    # Don't change markers
    FIXED = 0
    # Change markers to periodic ones
    PERIODIC = 1
    # Change markers to any
    RECOG = 2
    
def replace_syms(conf, pat, axis_states):
    "Replace a pattern in a configuration;"
    "return a new configuration and a boolean for changes."
    if all(conf[nvec] == sym for (nvec, sym) in pat.items()):
        return (False, conf)

    new_markers = []
    for (i, marker) in enumerate(conf.markers):
        if axis_states[i] == AxisState.FIXED:
            new_markers.append(marker)
        elif axis_states[i] == AxisState.PERIODIC:
            # markers are necessarily periodic
            (a, b, c, d) = marker
            #assert a == b and c == d <- this failed, I misunderstand something I guess
            for nvec in pat:
                if nvec[0][i] < a:
                    a = a-((a-nvec[0][i])//(c-a)+1)*(c-a)
                elif nvec[i] >= c:
                    c = c+((nvec[0][i]-c)//(c-a)+1)*(c-a)
            new_markers.append((a,a, c,c))
        elif axis_states[i] == AxisState.RECOG:
            # markers can be anything
            (a, b, c, d) = marker
            # first, expand markers
            if a == b:
                if c == d:
                    # fully periodic
                    a, d = a-(c-a), c+(c-a)
                else:
                    a = a-(c-b)
            elif c == d:
                d = c+(c-b)
            for nvec in pat:
                if nvec[0][i] < b:
                    new_b = b-((b-nvec[0][i])//(b-a))*(b-a)
                    a, b = new_b-(b-a), new_b
                elif nvec[0][i] >= c:
                    new_c = c+((nvec[0][i]-c)//(d-c)+1)*(d-c)
                    c, d = new_c, new_c+(d-c)
            new_markers.append((a,b,c,d))
    
    new_conf = conf.remark(new_markers)
    for (nvec, sym) in pat.items():
        new_conf.pat[nvec] = sym
    min_markers = new_conf.minimized_markers()
    new_conf.remark(min_markers)
    return (True, new_conf)

class TilerState:
    """
    A class that maintains an undoable state for tiler.
    It contains the current decorated configuration and selection.
    The nodes of the configuration are decorated with fixedness information.
    """
    
    def __init__(self, conf=None, selection=None, dim=None, nodes=None, alph=None, sizes=None, periodic=None):
        if conf is None: # sizes+periodic used if no initial config
            pat = {(vec, node,) : (list(alph[node]), False)
                   for vec in hyperrect([(0,sizes[d]) for d in range(dim)])
                   for node in nodes}
            if periodic is None:
                markers = None
            else:
                markers = [(0,0, sizes[d],sizes[d]) if p else None
                           for (d,p) in zip(range(dim),periodic)]
            conf = RecognizableConf(markers, pat, nodes, dim=dim)
        self.conf = conf
        if selection is None:
            selection = set()
        self.selection = selection

def decorate_default(conf):
    "Add default (False) decorations."
    if isinstance(conf, RecognizableConf):
        decor_pat = {nvec : (sym, False) for (nvec, sym) in conf.pat.items()}
        return RecognizableConf(conf.markers, decor_pat, conf.nodes, onesided=conf.onesided)
    elif isinstance(conf, AutomaticConf):
        return conf
        
def copy_decoration(undec_conf, dec_conf):
    """
    Make a configuration with contents of undec_conf and decorations of dec_conf.
    Assume they have same defined nodes.
    """
    decor_pat = dict()
    for (nvec, sym) in undec_conf.pat.items():
        sym2 = dec_conf[nvec]
        if sym is None:
            decor_pat[nvec] = None
        else: # sym2 should also not be None
            decor_pat[nvec] = (sym, sym2[1])
    return RecognizableConf(undec_conf.markers, decor_pat, undec_conf.nodes, onesided=undec_conf.onesided)
    
def undecorate(conf, unfix_atoms=False, alph=None):
    "Remove decorations. unfix_atoms replaces non-fixed singletons with the full list."
    #print("undecorating", conf.display_str())
    undec_pat = dict()
    for (nvec, tup) in conf.pat.items():
        if tup is None:
            undec_pat[nvec] = None
        else:
            sym, fix = tup
            # the len(sym) == 1 things is technical and about different representations
            if (type(sym) != list or len(sym) == 1) and not fix:
                undec_pat[nvec] = list(alph[nvec[-1]])
            elif type(sym) == list and len(sym) == 1:
                undec_pat[nvec] = sym[0]
            else:
                undec_pat[nvec] = sym
            #print("unfixed", tup, "at", nvec, "to", undec_pat[nvec])
    return RecognizableConf(conf.markers, undec_pat, conf.nodes, onesided=conf.onesided)

class TilerBackend:
    """
    A class that maintains the backend for tiler.
    It contains the ambient SFT and settings, the current state, and a history of states.
    """
    
    def __init__(self, sft, init_conf=None, sizes=None, periodic=None, project_to=None):
        self.sft = sft
        if init_conf is not None:
            init_conf = decorate_default(init_conf)
        self.history = [TilerState(conf=init_conf, dim=sft.dim, nodes=sft.nodes, alph=sft.alph, sizes=sizes, periodic=periodic)]
        self.history_index = 0
        self.axis_states = [AxisState.FIXED]*sft.dim
        self.clipboard = None
        if project_to is None:
            project_to = list(range(sft.dim))
        self.project_to = project_to
            
    def project(self, nvec):
        return (tuple(nvec[0][i] for i in self.project_to), nvec[-1])
        
    def deproject(self, nvec):
        return tuple(nvec[0][self.project_to.index(i)] if i in self.project_to else 0
                     for i in range(self.sft.dim)), nvec[-1]
        
    def conf(self):
        return self.history[self.history_index].conf
        
    def selection(self):
        return self.history[self.history_index].selection
        
    def undo(self):
        "Rewind into the previous stored state if possible, return a boolean."
        if self.history_index > 0:
            self.history_index -= 1
            return True
        else:
            return False
            
    def redo(self):
        "Advance into the next stored state if possible, return a boolean."
        if self.history_index < len(self.history) - 1:
            self.history_index += 1
            return True
        else:
            return False
            
    def update_state(self, new_state, save=True):
        "Update the state, keeping the history that's older than the current state."
        if save:
            self.history = self.history[:self.history_index+1]
            self.history.append(new_state)
            self.history_index += 1
        else:
            self.history = self.history[:self.history_index]
            self.history.append(new_state)
    
    def replace_conf(self, conf):
        "Replace the configuration with a new one, save the old state."
        self.update_state(TilerState(conf=conf, selection=self.selection(), dim=self.sft.dim, nodes=self.sft.nodes))
        
    def update_selection(self, selection, save=True):
        "Replace selection with a new one, save the old state."
        self.update_state(TilerState(conf=self.conf(), selection=selection), save=save)
        
    def deduce(self):
        """
        Deduce the configuration, save the old state.
        Unfixed non-list nodes are set to unknown before deduction.
        Return a Boolean for success.
        """
        

        #if self.conf().empty(): <- maybe smth like this is a good idea, since this fails with periodic right now.
        #    return
        
        
        
        fixed_axes = [i for (i,st) in enumerate(self.axis_states) if st == AxisState.FIXED and i in self.project_to]
        periodics = [i for (i,st) in enumerate(self.axis_states) if st == AxisState.PERIODIC and i in self.project_to]
        undec_conf = undecorate(self.conf(), unfix_atoms=True, alph=self.sft.alph)
        projection = RecognizableConf([undec_conf.markers[i] for i in self.project_to],
                                      {self.project(nvec) : sym for (nvec, sym) in undec_conf.pat.items()},
                                      self.sft.nodes,
                                      onesided=self.sft.onesided)
        #print("tiler deducing", projection.display_str())
        deduced_conf = self.sft.deduce_global(projection, periodics=periodics, fixed_axes=fixed_axes)
        #print("deduced",deduced_conf)
        if deduced_conf is not None:
            new_markers = undec_conf.markers[:]
            for (marker, ix) in zip(deduced_conf.markers, self.project_to):
                new_markers[ix] = marker
            deprojection = RecognizableConf(new_markers,
                                            {self.deproject(nvec) : sym
                                             for (nvec, sym) in deduced_conf.pat.items()},
                                            self.sft.nodes,
                                            onesided=self.sft.onesided)
            #print("it's", deduced_conf.display_str())
            decorated_conf = copy_decoration(deprojection, self.conf())
            self.replace_conf(decorated_conf)
            return True
        return False
            
    def minimize_markers(self):
        "Minimize the markers along each non-fixed axis, save the old state if changes were made."
        fixeds = [axis for (axis, st) in enumerate(self.axis_states) if st == AxisState.FIXED]
        conf = self.conf()
        mins = conf.minimized_markers(fixed_axes=fixeds)
        if mins != conf.markers:
            self.replace_conf(conf.remark(mins))

    def replace_patch(self, pat, keep_markers=False):
        "Replace patch in configuration, save the old state if changes were made."
        conf = self.conf()
        proj_pat = {self.project(nvec) : sym for (nvec, sym) in pat.items()}
        if keep_markers:
            old_axes = self.axis_states
            self.axis_states = [AxisState.FIXED]*self.sft.dim
        changed, conf = replace_syms(conf, proj_pat, self.axis_states)
        if changed:
            self.replace_conf(conf)
        if keep_markers:
            self.axis_states = old_axes
            
    def copy_selection(self):
        """
        Copy the current selection (translated to origin) to clipboard.
        Also remove the selection and save the state.
        """
        min_vec = [min(nvec[0][i] for nvec in self.selection())
                   for i in range(self.sft.dim)]
        self.clipboard = {nvsub(nvec, min_vec) : self.conf()[nvec]
                          for nvec in self.selection()}
        self.update_selection(set())
        
    def paste_clipboard(self, vec):
        "Paste a translated copy of the clipboard, and save the old state if changes were made."
        if self.clipboard is not None:
            self.replace_patch({nvadd(nvec, vec) : sym for (nvec, sym) in self.clipboard.items()})
            
    def toggle_axis(self, axis):
        "Toggle the state of an axis."
        st = self.axis_states[axis]
        conf = self.conf()
        if st == AxisState.FIXED:
            if conf.is_periodic(axis):
                new_st = AxisState.PERIODIC
            else:
                new_st = AxisState.RECOG
        elif st == AxisState.PERIODIC:
            new_st = AxisState.RECOG
        else:
            new_st = AxisState.FIXED
        self.axis_states[axis] = new_st
        
    def replace_markers(self, axis, new_markers):
        "Replace the markers on a given axis if valid, save the old state."
        conf = self.conf()
        a, b, c, d = new_markers
        if not (((a < b <= c < d) or (a==b < c==d)) and conf.compatible(axis, new_markers)):
            return
        markers = conf.markers[:]
        markers[axis] = new_markers
        new_conf = conf.remark(markers)
        if new_conf is not None:
            self.replace_conf(new_conf)
        
    def fix_nodes(self, nvecs):
        "Fix the given nodes, save if changes are made."
        pat = dict()
        for nvec in nvecs:
            (sym, _) = self.conf()[nvec]
            pat[nvec] = (sym, True)
        self.replace_patch(pat)
        
    def unfix_all(self):
        "Unfix all nodes, save if changes are made."
        pat = dict()
        for nvec in self.conf().pat:
            #print(nvec, self.conf()[nvec])
            if self.conf()[nvec] == None:
                continue
            (sym, _) = self.conf()[nvec]
            pat[nvec] = (sym, False)
        self.replace_patch(pat)

    def clear_deduced(self):
        "Reset deduced nodes to unknown."
        pat = dict()
        for (nvec, tup) in self.conf().pat.items():
            if tup is None:
                continue
            else:
                sym, fix = tup
                if fix == True:
                    continue
                # the len(sym) == 1 things is technical and about different representations
                if (type(sym) != list or len(sym) == 1) and not fix:
                    pat[nvec] = (list(self.sft.alph[nvec[-1]]), False)
                elif type(sym) == list and len(sym) == 1:
                    pat[nvec] = (sym[0], False)
        self.replace_patch(pat)

    """
    # this seems to be a duplicate of the above, which is unfinished and broken, TODO: remove
    def clear_deduced(self):
        "Reset deduced nodes to unknown."
        pat = dict()
        for nvec in self.conf().pat:
            if self.conf()[nvec] == None:
                continue
            (sym, fixed) = self.conf()[nvec]
            if fixed: continue
            pat[nvec] = (self.alpha, False)
        self.replace_patch(pat)
    """
        
    def clear_all(self, also_nonexisting):
        "Set all nodes to unknown, save if changes are made."
        pat = dict()
        for nvec in self.conf().pat:
            if not also_nonexisting and self.conf().pat[nvec] is None:
                continue
            syms = list(self.sft.alph[nvec[-1]])
            pat[nvec] = (syms, False)
        self.replace_patch(pat, keep_markers=True)

    def remove_all(self):
        "Set all nodes to empty, save if changes are made."
        pat = dict()
        for nvec in self.conf().pat:
            pat[nvec] = None
        self.replace_patch(pat)
