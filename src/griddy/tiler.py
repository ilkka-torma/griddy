#from language3 import *
import math
import compiler2
import sft
import pygame
import configuration
from tiler_backend import *
#import pygame_textinput
import pygame_gui
import time
import numpy as np
from numpy.linalg import inv
import os
import re
from enum import Enum

"""
nodes = [0]
dim = 2
topology = [("up", (0,0,0), (0,1,0)),
            ("dn", (0,0,0), (0,-1,0)),
            ("rt", (0,0,0), (1,0,0)),
            ("dn", (0,0,0), (-1,0,0))]
alphabet = [0, 1]
# golden mean shift
c = compiler.formula_to_circuit(nodes = nodes, # N = nodes
                       dim = dim, # dimension
                       topology = topology, # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = alphabet,
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("NODEFORALL", "v", {"o" : 1},
                                   ("SETCIRCUIT", "c", ("F",),
                                    ("OR", ("HASVAL", "o", 0),
                                    ("POSEQ", "o", "v"),
                                    ("HASVAL", "v", 0),
                                     ("CIRCUIT", "c"))))))

the_SFT = sft.SFT(dim, nodes, alphabet, forbs=None, circuit=c)

"""


#from constraint import *
#from ortools.sat.python import cp_model
#from ortools.constraint_solver import pywrapcp

#import threader
#import threading
#import traceback
#from multiprocessing import Process, Queue

# Define some colors
BLACK = (0, 0, 0)
WHITE = (255, 255, 255)
GREEN = (0, 255, 0)
BLUE = (0, 0, 255)
YELLOW = (255, 255, 0)
GRAY = (120, 120, 120)

# UNKNOWN means we deduce the color
# EMPTY
UNKNOWN = "UNKNOWN" # not set by user, should deduce
EMPTY = "EMPTY" # cell is not used -- actually we just erase these from grid but useful for drawcolor
DEDUCED = "DEDUCED" # not set by user, some value has been deduced
SET = "SET" # set by user
FIXITY = "FIXITY" # fixity of node

TILING_OK_GRID_COLOR = (30,30,30)
TILING_BAD_GRID_COLOR = (100, 50, 50)
TILING_UNKNOWN_GRID_COLOR = (50,50,50)

#deduced_colors = {0 : (150, 150, 150), 1 : (50, 130, 50),
#                  2 : (16,56,190), 3: (85, 111, 222),
#                  4: (190, 180, 170)}

UNKNOWN_COLOR = GRAY
EMPTY_COLOR = BLACK # actually we just don't draw these



# number meanings in grid: 0 = not there, 1 = there,
# 2 = unknown, 3 = not there deduced, 4 = there deduced
# None/not in the dict = not part of grid even

TILING_UNKNOWN = 0
TILING_OK = 1
TILING_BAD = 2

class CursorState(Enum):
    PAINT = 0
    MOVE_MARKERS = 1


def deduce_a_tiling(grid, the_SFT, x_period, y_period):

    raise Exception("deduce_a_tiling should never be called, use backend.")

    global currentstate
    currentstate = TILING_UNKNOWN

    for g in grid:
        if grid[g] != UNKNOWN and grid[g][0] == DEDUCED:
            grid[g] = UNKNOWN

    pat = {}

    # grid is a dict from (x, y, n) to v where n is actual name of node, and v actual symbol name
    for g in grid:
        if the_SFT.dim == 1 and g[1] != 0:
            continue
        if grid[g] != UNKNOWN:
            assert grid[g][0] == SET
            try:
                val = the_SFT.alph[g[-1]][grid[g][1]]
            except:
                print(g)
                print(the_SFT.alph)
                print(grid[g])
                a = bbb
            if the_SFT.dim == 1:
                pat[(g[0], g[-1])] = val
            else:
                #known_values[flipy(g)] = val
                pat[g] = val
            #print("known", g, val)
        elif the_SFT.dim == 1:
            pat[(g[0], g[-1])] = list(the_SFT.alph[g[-1]])
        else:
            #domain.add(flipy(g[:-1]))
            pat[g] = list(the_SFT.alph[g[-1]])
            #print("unknown", g)
            
    #print("domain", domain)
    #print("known", known_values)        

    #print("deducing model")
    
    conf = configuration.RecognizableConf([x_period, y_period], pat, the_SFT.nodes)
    #print("tiler deducing", conf.display_str())

    model = the_SFT.deduce_global(conf)

    print("model found", model.display_str())

    if model == None:
        currentstate = TILING_BAD
    else:
        currentstate = TILING_OK

        for g in grid:
            if grid[g] == UNKNOWN:
                val = model[g]
                print("model maps", d, "to", val)
                
                if val != None:
                    # here b {(0, 0): ['a', 'b', 'c']} (10, 10, (0, 0))
                    #here c {('D', 0): ['a', 'b', 'c'], ('C', 0): [0, 1]} (10, 10, ('C', 0))

                    #print("here", val, the_SFT.alph, d)
                    grid[g] = (DEDUCED, the_SFT.alph[g[-1]].index(val))
                else:
                    grid[g] = UNKNOWN
                #print(d, "in model", grid[dd])

def vadd(u, v):
    return u[0] + v[0], u[1] + v[1]
def vsub(u, v):
    return u[0] - v[0], u[1] - v[1]
def smul(s, u):
    return s*u[0], s*u[1]
def vmul(u, v):
    return u[0]*v[0], u[1]*v[1]
def distance(u, v):
    w = vsub(u, v)
    return math.sqrt(w[0]*w[0] + w[1]*w[1])

def flipy(t):
    return (t[0], -t[1]) + t[2:]

# coordinate preprocess to screen
def cp_to_screen(v):
    return v[0], screenheight-v[1]
# coordinate preprocess from screen
def cp_from_screen(v):
    return v[0], screenheight-v[1]

def get_picture(p):
    for typ in ["", ".png", ".jpg", ".gif"]:
        path = p + typ
        if os.path.exists(path):
            return pygame.image.load(path)
    if "_" not in p:
        raise Exception("Image %s does not exist." % p)
    pos = p.rindex("_")
    if p[pos+1] != "r":
        raise Exception("Incorrect image transformation syntax in %s, try filename_r90." % p)
    angle = int(p[pos+2:])
    filename = p[:pos]
    pic = get_picture(filename)
    return pygame.transform.rotate(pic, angle)

"""
# newer pygame should have scale_by
def scale_picture(pic, factor):
    size = pic.get_width(), pic.get_height()
    # consider dest_surface?
    return pygame.transform.scale(pic, (max(1, int(size[0]*factor)), max(1, int(size[1]*factor))))
"""

def ok_file(s):
    return len(s) >= 1 # s[-5:] == ".ptrn" or len(p )

def save(grid, filename):
    if filename[:-5] != ".ptrn":
        filename = filename + ".ptrn"
    with open(filename, "w") as fil:
        for (x, y, n) in grid:
            #print((x,y,n), "was", grid[(x,y,n)])
            # for ease-of-use, we print out an ASCII table
            fil.write("%s: %s\n" % ((x, y, n), grid[(x, y, n)]))

def load(grid, filename):
    if filename[:-5] != ".ptrn":
        filename = filename + ".ptrn"
    for n in list(grid.keys()):
        del grid[n]
    with open(filename, "r") as fil:
        for line in fil:
            a, b = line.split(": ")[:2]
            #print(a, b)

            # for safety, we parse manually
            a = re.match("\((\-?[0-9]+), (\-?[0-9]+), ([\'a-zA-Z0-9_]+)\)", a)
            a = int(a[1]), int(a[2]), a[3]
            
            if a[2][0] == "'":
                a = a[0], a[1], a[2][1:-1]
            else:
                # for some reason our convention with integer nodes is to use python ints
                a = a[0], a[1], int(a[2])
            #print(a)

            if b.strip() == UNKNOWN:
                grid[a] = UNKNOWN
            else:
                b = re.match("\(\'([A-Z]+)\', ([0-9]+)\)", b)
                set_or_ded, idx = b[1], b[2]
                grid[a] = set_or_ded, int(idx)
            #print(b)                
            #print(a, "now", grid[a])

# In a configuration, (None, ...) can also denote a None symbol, this is for that.
def Noneish(a):
    return a == None or type(a) == tuple and a[0] == None

#print(re.match("\((\-?[0-9]+), (\-?[0-9]+), ([\'a-zA-Z0-9_]+)\)", "(29, 9, 'top'))"))

#a = bbb

def run(the_SFT, topology, gridmoves, nodeoffsets,
        x_size=10, y_size=10, x_periodic=False, y_periodic=False,
        pictures=None, the_colors=None, initial=None, hidden_nodes=[]):
    #print(topology)

    # check dimension in the first command of topology
    dimension = len(topology[0][1]) # - 1
    print("dimension %s" % dimension)
    #print("dimension %s" % dimension)
    # we force topology 2-dimensional
    if dimension == 1:
        #print(topology)
        newtopology = []
        for t in topology:
            #print(t)
            newtopology.append((t[0], (0, t[1]), t[2], t[3])) #(t[0],) + tuple(i[:-1] + (0, i[-1]) for i in t[1:]))
        #print (newtopology)
        topology = newtopology
    elif dimension not in [1, 2]:
        raise Exception("Tiler only supports dimensions 1 and 2, not %s." % dimension)

    if initial is not None and dimension != initial.dim:
        raise Exception("Dimension mismatch between tiler and initial configuration: {} vs {}".format(dimension, initial.dim))
        

    print("hidden nodes", hidden_nodes)

    #if dimension == 2:
    #y_range = list(range(-r, r+1))
    #else:
    #    dimension_y_range = [0]

    #print(pictures)

    
    
    #print(gridmoves)
    #print(nodeoffsets)
    #print("mus")
    global nodes
    nodes = list(the_SFT.nodes) #list(n for n in the_SFT.nodes)
    if any(node in nodeoffsets for node in nodes) and any(node not in nodeoffsets for node in nodes):
        for n in nodes:
            if n not in nodeoffsets:
                raise Exception("All or none of nodes should have offsets specified ({} missing).".format(n))
    for node in nodeoffsets:
        if node not in nodes:
            print("Unknown node in offsets ({}); using default offsets instead".format(node))
    #if nodeoffsets == {} or nodeoffsets == None:
    #    nodeoffsets = {node : (i/(len(nodes)+1), i/(len(nodes)+1)) for (i, node) in enumerate(nodes)}
    runningoffset = 0
    for n in nodes:
        if n not in nodeoffsets and n not in hidden_nodes:
            # this only makes sense if either all or none are set
            nodeoffsets[n] = (0, runningoffset)
            runningoffset += 1/len(nodes)
    #print("nodes and offsets", nodes, nodeoffsets)
    dim = the_SFT.dim
    alphabets = the_SFT.alph
    
    # make colors
    if the_colors is not None:
        colors = {}
        for node in nodes:
            for sym in alphabets[node]:
                colors[node, sym] = the_colors[sym]
    else:
        
        # colors used for alphabet symbols, and tinted versions for deduced ones
        ix_colors = {
          0 : WHITE, 1 : (255,0,0), 2 : (0,255,0), 3 :(0,0,255),
          4 : (255,255,0), 5 : (255,0,255), 6 : (0,255,255),
          7 : (255, 80, 80), 8 : (80, 255, 80), 9 : (80, 80, 255),
          10 : (255, 160, 160), 11 : (160, 255, 160), 12 : (160, 160, 255),
          13 : (80, 160, 255), 14 : (160, 255, 80), 15 : (255, 80, 160)
          }
        colors = {}
        for node in nodes:
            
            for (i, sym) in enumerate(alphabets[node]):
                print("coloring", node, sym, i, ix_colors[i % len(ix_colors)])
                print(node, sym)
                colors[node, sym] = ix_colors[i]
    deduced_colors = {}
    for c in colors:
        deduced_colors[c] = tuple(map(lambda a:a//2, colors[c]))

    print("nodes", nodes)
    print("alph", alphabets)
    print("colors", colors)

    origin = ((0,)*dimension), nodes[0]

    #que = Queue()

    currentstate = TILING_UNKNOWN
    
    cursor_state = CursorState.PAINT

    # This sets the positions of nodes in grid cells.
    # This is done after transformation.
    #nodeoffsets = {0 : (0,0)} #{0 : (0.25, 0.75), 1: (0.75, 0.25)}

    # Shearing and stuff, i.e. what is x & y movement in grid visually
    #gridmoves = [(1, 0), (0, 1)]
     
    # This sets the margin between each cell
    #MARGIN = 3

    #gridheight = 15
    #gridwidth = 15
    
    camera = (x_size/2, y_size/2) # where we looking; center of screen is here
    zoom = (40, 40) # how big are cells basically

    linknodesizeandzoom = True
    shouldnodesize = 12
    ratio = shouldnodesize/zoom[0]
    
    global screenwidth, screenheight
    screenwidth = 700
    screenheight = 500

    pygame.font.init() 
    my_font = pygame.font.SysFont('Consolas', 30)
    msg_font = pygame.font.SysFont('Consolas', 15)
    
    print("size", x_size, y_size)
    
    # initialize backend
    backend = TilerBackend(the_SFT, init_conf=initial, sizes=[x_size,y_size], periodic=[x_periodic,y_periodic])
     
    # our grid is now just all initial_state
    #grid = {}
    #for x in range(0, x_size):
    #    for y in range(0, y_size):
    #        # EMPTY means we'll try to deduce a color here
    #        for n in nodes: #range(len(nodes)):
    #            if initial is None:
    #                grid[(x, y, n)] = UNKNOWN
    #            elif initial.dim == 1:
    #                grid[(x, y, n)] = (SET, initial[x, n])
    #            else:
    #                grid[(x, y, n)] = (SET, initial[x, y, n])
    #grid[(0, 0, nodes[0])] = (SET, 1)
    #grid[(1, 0, nodes[0])] = (SET, 1)
    # print(grid)

    nodepositions = {}
     
    # Initialize pygame
    pygame.init()
     
    # Set the HEIGHT and WIDTH of the screen
    WINDOW_SIZE = [screenwidth, screenheight]
    screen = pygame.display.set_mode(WINDOW_SIZE, pygame.RESIZABLE)
    manager = pygame_gui.UIManager(WINDOW_SIZE)
     
    # Set title of screen
    pygame.display.set_caption("Tiler")

    print("pictures", pictures)
    
    if pictures != None:
        pictures = {node : {sym : get_picture(pic) for (sym, pic) in zip(alphabets[node], pics)}
                    for (node, pics) in pictures.items()}
    
    print("pictures2", pictures)
    
    # Loop until the user clicks the close button.
    done = False
    
    # Used to manage how fast the screen updates
    clock = pygame.time.Clock()

    mouseisdown = False
    mouserisdown = False
    drawcolor = None
    

    thred = None


    boxx = 300
    boxy = 20

    filename_box = pygame_gui.elements.UITextEntryLine(pygame.Rect((boxx, boxy), (100, 50)),
                                                        manager=manager,
                                                        object_id="#filename")
    filename_box.set_text("conf")

    save_button = pygame_gui.elements.UIButton(relative_rect=pygame.Rect((boxx, boxy+60), (60, 50)),
                                             text='save',
                                             manager=manager)
    load_button = pygame_gui.elements.UIButton(relative_rect=pygame.Rect((boxx+60, boxy+60), (60, 50)),
                                             text='load',
                                             manager=manager)

    ui_things = [filename_box, save_button, load_button]

    """
    #manager = pygame_textinput.TextInputManager(validator)
    textinput = pygame_textinput.TextInputVisualizer(font_object = msg_font)
    textinput.cursor_width = 4
    textinput.cursor_blink_interval = 399
    textinput.antialias = True
    textinput.font_color = (10,10,10)
    """
    
    

    def to_screen(x, y):
        if False and dimension == 1:
            return vadd((screenwidth/2, screenheight/2), smul((x - camera[0])*zoom[0], gridmoves[0]))
        else: # dimension == 2:
            return vadd((screenwidth/2, screenheight/2), vadd(smul((x - camera[0])*zoom[0], gridmoves[0]), smul((y - camera[1])*zoom[1], gridmoves[1])))            
    
    def to_grid(u, v):
        if False and dimension == 1:
            # ignore v
            #u = vadd((screenwidth/2, screenheight/2), smul((x - camera[0])*zoom, gridmoves[0]))
            pass
        
        else: # dimension == 2:
            """
            u, v = vadd((screenwidth/2, screenheight/2), vadd(smul((x - camera[0])*zoom, gridmoves[0]), smul((y - camera[1])*zoom, gridmoves[1])))
            vsub((u, v), vadd((screenwidth/2, screenheight/2)) = vadd(smul((x - camera[0])*zoom, gridmoves[0]), smul((y - camera[1])*zoom, gridmoves[1]))
            let (U, V) = vsub((u, v), (screenwidth/2, screenheight/2))
            (X, Y) = (x - camera[0])*zoom, (y - camera[1])*zoom
            of course x = X/zoom + camera[0], y = Y/zoom + camera[1]
            then
            (U, V) = vadd(smul(X, gridmoves[0]), smul(Y, gridmoves[1]))
            so consider matrix with M columns gridmoves[0], gridmoves[1] and column vector XY = (X, Y)
            then (U, V) = M XY
            we should invert this matrix M to get some MI
            then MI (U, V) = X, Y
            """
            a, b = gridmoves[0][0], gridmoves[1][0]
            c, d = gridmoves[0][1], gridmoves[1][1]
            M = np.array([gridmoves[0], gridmoves[1]]).transpose()
            MI = inv(M)
            U, V = vsub((u, v), (screenwidth/2, screenheight/2))
            XY = np.matmul(MI, np.array([[U], [V]])).transpose()
            assert XY.shape == (1, 2)
            XY = XY[0]
            #A, B = d, -b
            #C, D = -c, a
            #st = smul(1/zoom, vsub((u, v), (screenwidth/2, screenheight/2)))
            x = XY[0]/zoom[0] + camera[0]
            y = XY[1]/zoom[1] + camera[1]
            #return A*st[0] + B*st[1], C*st[0] + D*st[1]
            return x, y

    # given grid coords, find closest (non-hidden) node; node is given as its index
    # seems to assume that offset vectors not too large
    def get_node(x, y, debug_prints = False):
        if debug_prints:
            print()
            print("getting")
            print(x, y)
            
        closest = None
        dist = 10000
        rr = 2
        for x0 in range(math.floor(x) - rr, math.floor(x) + rr + 1):
            for y0 in list(range(math.floor(y) - rr, math.floor(y) + rr + 1)):
                for n in range(len(nodes)):
                    if nodes[n] in hidden_nodes:
                        continue
                    d = distance(vadd(to_screen(x0, y0), vmul(zoom, nodeoffsets[nodes[n]])), to_screen(x, y))
                    #if debug_prints:
                    #    print(x0, y0, n, vadd(to_screen(x0, y0), smul(zoom,nodeoffsets[nodes[n]]), d, x, y)
                    if d < dist:
                        dist = d
                        closest = ((x0, y0), n)
        return closest
        
        
    # given corners of screen rectangle, find all (non-hidden) nodes inside
    def get_nodes_in_rect(u1, v1, u2, v2):
        # screen corners to grid
        xmin, ymin = to_grid(min(u1,u2), min(v1,v2))
        xmax, ymax = to_grid(max(u1,u2), max(v1,v2))
        xmin = int(xmin-5)
        ymin = int(ymin-5)
        xmax = int(xmax+5)
        ymax = int(ymax+5)
        
        res = []
        # just filter the nodes
        for x in range(xmin, xmax+1):
            for y in range(ymin, ymax+1):
                for n in range(len(nodes)):
                    if nodes[n] in hidden_nodes:
                        continue
                    nodeu, nodev = vadd(to_screen(x, y), vmul(zoom, nodeoffsets[nodes[n]]))
                    if min(u1,u2) <= nodeu <= max(u1,u2) and min(v1,v2) <= nodev <= max(v1,v2):
                        res.append(((x,y),n))
        
        return res
    # print(get_node(0,7))

    def mouse_on_ui(mpos):
        for u in ui_things:
            r = u.relative_rect
            x, y, w, h = r
            if mpos[0] >= x and mpos[0] < x+w and mpos[1] >= y and mpos[1] < y+h:
                return True
        return False

    draw_grid_lines = True
    nnn = 0

    tim = time.time()
    
    show_help = True
    show_labels = True
    
    if isinstance(backend.conf, RecognizableConf):
        show_markers = True
    else:
        show_markers = False
    
    selection_anchor = None
    selection = set()
    
    moving_marker = None
    
    moving_camera = False
    
    paint_fixity = True

    
    #for nvec in backend.conf().pat:
    #    print(nvec, backend.conf()[nvec])
    
    # -------- Main Program Loop -----------
    while not done:
        mousechanged = False
        mouserchanged = False
        pasting = False
        #print("main looppo")
        new_tim = time.time()
        time_delta = new_tim - tim
        tim = new_tim
        
        nnn += 1

        mouse_displacement = (0,0)

        #vemmel = set()
        #gimmel = {}

        """
        if not que.empty():
            currentstate = que.get()
            grid = que.get()
            if currentstate == TILING_OK:
                print ("deduction successful")
            if currentstate == TILING_BAD:
                print ("deduction FAILED")
            # thread has ended by protocol
            thred.join()
            thred = None
        """


        events = pygame.event.get()
        #textinput.update(events)

        focus_set = manager.get_focus_set()
        # if UI is used, we should not use mouse or key inputs for other things
        cancel_non_UI = False
        if focus_set == None:
            pass
        else:
            assert len(focus_set) == 1
            focused = list(focus_set)[0]
            # we want some focuses to steal input, let's just use the object type
            if type(focused) == pygame_gui.elements.ui_text_entry_line.UITextEntryLine:
                cancel_non_UI = True # TODO: IGNORE THINGS WHEN TRUE, AND DO SAVES

        shift_modifier = bool(pygame.key.get_mods() & pygame.KMOD_SHIFT)
        ctrl_modifier = bool(pygame.key.get_mods() & pygame.KMOD_CTRL)
        any_modifier = shift_modifier or ctrl_modifier
        mpos = pygame.mouse.get_pos()

        zoommul = 1
        
        for event in events:  # User did something

            manager.process_events(event)

            if event.type == pygame_gui.UI_BUTTON_START_PRESS and show_help:
                    
                cancel_non_UI = True
                #print("canceling")
                filename = filename_box.get_text()
                if not ok_file(filename):
                    print("Filename %s is not valid; for safety, we require length at least 1." % filename)
                else:
                    if event.ui_element == save_button:
                        save(grid, filename)
                        print('Configuration saved in %s.' % filename)
                    if event.ui_element == load_button:
                        load(grid, filename)
                        print('Configuration loaded from %s.' % filename)
            
            if event.type == pygame.QUIT:  # If user clicked close
                done = True  # Flag that we are done so we exit this loop
                
            elif event.type == pygame.KEYDOWN and not cancel_non_UI:

                drawcolor_set = False
                if event.key == pygame.K_1:
                    drawcolor = (SET, 0)
                    drawcolor_set = True
                if event.key == pygame.K_2:
                    drawcolor = (SET, 1)
                    drawcolor_set = True
                if event.key == pygame.K_3:
                    drawcolor = (SET, 2)
                    drawcolor_set = True
                if event.key == pygame.K_4:
                    drawcolor = (SET, 3)
                    drawcolor_set = True
                if event.key == pygame.K_5:
                    drawcolor = (SET, 4)
                    drawcolor_set = True
                if event.key == pygame.K_6:
                    drawcolor = (SET, 5)
                    drawcolor_set = True
                if event.key == pygame.K_7:
                    drawcolor = (SET, 6)
                    drawcolor_set = True
                if event.key == pygame.K_8:
                    drawcolor = (SET, 7)
                    drawcolor_set = True
                if event.key == pygame.K_9:
                    drawcolor = (SET, 8)
                    drawcolor_set = True
                if event.key == pygame.K_0:
                    drawcolor = (SET, 9)
                    drawcolor_set = True
                if event.key == pygame.K_f:
                    drawcolor = FIXITY # means unused
                    drawcolor_set = True
                if event.key == pygame.K_u:
                    drawcolor = UNKNOWN # means unused
                    drawcolor_set = True
                if event.key == pygame.K_BACKSPACE:
                    if shift_modifier:
                        backend.remove_all()
                    else:
                        drawcolor = EMPTY
                        drawcolor_set = True
                        
                sel = backend.selection()
                if drawcolor_set and sel:
                    patch = dict()
                    if drawcolor == FIXITY:
                        paint_fixity = None
                        conf = backend.conf()
                        for ((x,y),n) in sel:
                            val = conf[(x,y),nodes[n]]
                            if val is not None:
                                paint_fixity = False
                                if not val[1]:
                                    paint_fixity = True
                                    break
                        if paint_fixity is not None:
                            for ((x,y),n) in sel:
                                val = conf[(x,y),nodes[n]]
                                if val is not None and (type(val) != list or len(val) == 1):
                                    patch[(x,y),nodes[n]] = (val[0], paint_fixity)
                    else:
                        for ((x,y),n) in sel:
                            if drawcolor == EMPTY:
                                patch[(x,y),n] = None
                            elif drawcolor == UNKNOWN:
                                patch[(x,y),n] = (list(the_SFT.alph[n]), False)
                            else:
                                if drawcolor[1] < len(the_SFT.alph[n]):
                                    patch[(x,y),n] = (the_SFT.alph[n][drawcolor[1]], True)
                    
                    backend.replace_patch(patch)
                    currentstate = TILING_UNKNOWN
                    #backend.update_selection(set(), save=False)

                if event.key == pygame.K_c:
                    if not any_modifier: # x-axis state
                        backend.toggle_axis(0)
                    if ctrl_modifier: # copy from selection
                        backend.copy_selection()
                if event.key == pygame.K_v:
                    if not any_modifier: # y-axis state
                        backend.toggle_axis(1)
                    if ctrl_modifier: # paste from clipboard
                        pasting = True
                if event.key == pygame.K_m and not ctrl_modifier:
                    backend.minimize_markers()
                if event.key == pygame.K_m and ctrl_modifier:
                    show_markers = not show_markers
                    
                if event.key == pygame.K_h:
                    if not ctrl_modifier:
                        show_help = not show_help
                    else:
                        draw_grid_lines = not draw_grid_lines
                if event.key == pygame.K_l:
                    show_labels = not show_labels
                    
                if event.key == pygame.K_e:
                    if shift_modifier and ctrl_modifier:
                        backend.clear_all(True)
                    elif shift_modifier:
                        backend.clear_all(False)
                    else:
                        backend.clear_deduced()
                        
                if event.key == pygame.K_d:
                    if cursor_state == CursorState.PAINT:
                        cursor_state = CursorState.MOVE_MARKERS
                    else:
                        cursor_state = CursorState.PAINT
                        moving_marker = None

                if event.key == pygame.K_z and ctrl_modifier:
                    backend.undo()
                if event.key == pygame.K_y and ctrl_modifier:
                    backend.redo()
                
                if event.key == pygame.K_ESCAPE:
                    if thred != None:
                        thred.terminate()
                        thred = None
                        print ("deduction cancelled")
                if event.key == pygame.K_SPACE:
                    if thred != None:
                        thred.terminate()
                        thred = None
                        print ("deduction cancelled")

                    print ("Tiling started.")
                    tim = time.time()
                    #thred = Process(target=deduce_a_tiling_threaded, args=(que, grid, gridheight, gridwidth))
                    #thred.start()

                    #deduce_a_tiling(grid, the_SFT, x_period = x_size if x_periodic else None, y_period = y_size if y_periodic else None)
                    success = backend.deduce()
                    if success:
                        currentstate = TILING_OK
                    else:
                        currentstate = TILING_BAD

                    print ("Tiling process finished in %s seconds." % (time.time() - tim)) # deduce_a_tiling returned (debug print)")

            elif event.type == pygame.MOUSEMOTION and moving_camera:
                mouse_displacement = event.rel
                    
            elif event.type == pygame.MOUSEBUTTONDOWN:
                # even if using _START_PRESS in _gui, mouse events come one iteration later
                # than in pygame, so we just do an explicit check...
                if not mouse_on_ui(mpos):
                    if event.button == 1: # left mouse button
                        if not mouseisdown:
                            mousechanged = True
                        mouseisdown = True
                    elif event.button == 2: # middle mouse button
                        moving_camera = True
                    elif event.button == 3: # right mouse button
                        if not mouserisdown:
                            mouserchanged = True
                        mouserisdown = True
                    
            elif event.type == pygame.MOUSEBUTTONUP:
                if event.button == 1:
                    if mouseisdown:
                        mousechanged = True
                    mouseisdown = False
                elif event.button == 2:
                    moving_camera = False
                elif event.button == 3: # right mouse button
                    if mouserisdown:
                        mouserchanged = True
                    mouserisdown = False
                
            elif event.type == pygame.VIDEORESIZE:
                # There's some code to add back window content here.
                screenwidth, screenheight = event.w, event.h
                WINDOW_SIZE = [screenwidth, screenheight]
                
                screen = pygame.display.set_mode(WINDOW_SIZE, pygame.RESIZABLE)
                # should probably also tell UI?

            if event.type == pygame.MOUSEWHEEL:
                #print(event.x, event.y)
                #zoom = smul(1.01 ** event.y, zoom) # note that there is also zoom code elsewhere
                zoommul *= 1.01 ** event.y
                
            # end of event loop

        #shift_modifier = bool(pygame.get_mod() & pygame.KMOD_SHIFT)
        #ctrl_modifier = bool(pygame.get_mod() & pygame.KMOD_CONTROL)
        #ny_modifier = shift_modifier or ctrl_modifier

        

        manager.update(time_delta)
            
        keys=pygame.key.get_pressed()
        screenmove = (0, 0)
        if not cancel_non_UI:
            if keys[pygame.K_LEFT]:
                screenmove = (-1, 0)
            if keys[pygame.K_RIGHT]:
                screenmove = (1, 0)
            if keys[pygame.K_UP]:
                screenmove = (0, 1)
            if keys[pygame.K_DOWN]:
                screenmove = (0, -1)
        if moving_camera:
            screenmove = (-mouse_displacement[0], mouse_displacement[1])
            
        #screenmove = smul(zoom*0.01, screenmove)
        shiftcoeff = 1
        if shift_modifier:
            shiftcoeff = 4
        screenmove = smul(shiftcoeff * 4, screenmove)
        gridmove = vsub(to_grid(*screenmove), to_grid(0, 0))
        
        camera = vadd(camera, gridmove)
        if not cancel_non_UI:
            # note that there is also zoom code elsewhere
            if (keys[pygame.K_a] and not any_modifier):
                zoommul *= 1.03 # = smul(1.01, zoom)
            if keys[pygame.K_z] and not any_modifier:
                zoommul /= 1.03 # = smul(1/1.01, zoom)
            
            if keys[pygame.K_s] and not any_modifier:
                shouldnodesize += 1
                ratio = shouldnodesize/zoom[0]
            if keys[pygame.K_x] and not any_modifier:
                shouldnodesize -= 1
                if shouldnodesize <= 1:
                    shouldnodesize = 1
                ratio = shouldnodesize/zoom[0]


        zoom = smul(zoommul, zoom)
        if linknodesizeandzoom:
            # recall ratio = nodesize/zoom
            shouldnodesize = ratio*zoom[0]
            nodesize = int(shouldnodesize)
            if nodesize == 0:
                nodesize = 1
            
            
        pos = cp_from_screen(mpos)
        #print(pos)
        pos = to_grid(*pos)
        #print(pos)
        #print(to_screen(*pos), pos, pygame.mouse.get_pos())
        node = get_node(*pos) #, mouseisdown)
        #if mouseisdown:
        #    assert gimmel[0] != None
        #if node != None:
        #    print(node)
        """
        if mousecolumn < 0: mousecolumn = 0
        if mousecolumn >= gridwidth: mousecolumn = gridwidth-1
        if mouserow < 0: mouserow = 0
        if mouserow >= gridheight: mouserow = gridheight-1
        """
        
        if pasting and node != None:
            (x, y), _ = node
            backend.paste_clipboard((x,y))

        # cases where grid is perhaps clicked
        if cursor_state == CursorState.PAINT and node != None and mouseisdown and drawcolor != None and not cancel_non_UI:
            #period_ok = True
            #if x_periodic:
            #    if node[0] < 0 or node[0] >= x_size:
            #        period_ok = False
            #if y_periodic:
            #    if node[1] < 0 or node[1] >= y_size:
            #        period_ok = False
            # cases where we should change
            currentstate = TILING_UNKNOWN
            node = (node[0], nodes[node[-1]])
            if drawcolor == EMPTY:
                patch = {node : None}
                for n in hidden_nodes: # TODO: this is repeated many times
                    patch[node[0], n] = None
                
                backend.replace_patch(patch)
            elif drawcolor == UNKNOWN:
                patch = {node : (list(alphabets[node[-1]]), False)}
                for n in hidden_nodes: # TODO: this is repeated many times
                    patch[node[0], n] = (alphabets[n], False)
                backend.replace_patch(patch)
            elif drawcolor == FIXITY:
                conf = backend.conf()
                if mousechanged:
                    val = backend.conf()[node]
                    if val is None or (type(val[0]) == list and len(val[0]) > 1):
                        paint_fixity = None
                    else:
                        paint_fixity = not val[1]
                if paint_fixity is not None and conf[node] is not None:
                    backend.replace_patch({node : (conf[node][0], paint_fixity)})
            elif drawcolor[0] == SET and drawcolor[1] < len(alphabets[node[-1]]):
                
                patch = {node : (alphabets[node[-1]][drawcolor[1]], True)}
                for n in hidden_nodes:
                    patch[node[0], n] = (alphabets[n], False)
                print("replacing", patch)
                backend.replace_patch(patch)
                    

                #print(node, drawcolor)
                if thred != None:
                    thred.terminate()
                    thred = None
                    print ("deduction cancelled")
                   
        if not cancel_non_UI:
            if mouserisdown:
                if mouserchanged:
                    selection_anchor = (mpos[0], screenheight-mpos[1])
                if selection_anchor is not None:
                    u1, v1 = mpos
                    u2, v2 = selection_anchor
                    selection = set(((x,y),nodes[n]) for ((x,y),n) in get_nodes_in_rect(u1, screenheight-v1, u2, v2))
            elif mouserchanged:
                if shift_modifier:
                    backend.update_selection(backend.selection() | selection)
                elif ctrl_modifier:
                    backend.update_selection(backend.selection() - selection)
                else:
                    backend.update_selection(selection)
                selection_anchor = None
                selection = set()

        if node is not None and mouseisdown and mousechanged and cursor_state == CursorState.MOVE_MARKERS and not cancel_non_UI:
            (x, y), _ = node
            if moving_marker is None:
                for (axis, marker) in enumerate(backend.conf().markers):
                    if any([x,y][axis] == mark for mark in marker):
                        moving_marker = (axis, [])
                        break
            else:
                axis, marker = moving_marker
                marker.append([x,y][axis])
                if len(marker) == 4:
                    marker.sort()
                    backend.replace_markers(axis, tuple(marker))
                    moving_marker = None
                    currentstate = TILING_UNKNOWN
        
        if not mouseisdown:
            paint_fixity = None

        # screen corners to grid
        xmin, ymin = to_grid(0, 0)
        xmin = math.floor(xmin-5)
        ymin = math.floor(ymin-5)

        xmax, ymax = to_grid(screenwidth, screenheight)
        xmax = math.ceil(xmax+5)
        ymax = math.ceil(ymax+5)
        #print(xmin, ymin, xmax, ymax)
     
        # Set the screen background
        if currentstate == TILING_UNKNOWN:
            screen.fill(TILING_UNKNOWN_GRID_COLOR)
        if currentstate == TILING_OK:
            screen.fill(TILING_OK_GRID_COLOR)
        if currentstate == TILING_BAD:
            #print "pad"
            screen.fill(TILING_BAD_GRID_COLOR)

        
        conf = backend.conf()
                
        #if nnn%1 == 0:
        #    print("backend conf", conf.display_str())
        
        # Draw the grid lines i.e. draw the edges
        if draw_grid_lines:
            for x in range(xmin, xmax + 1):
                for y in range(ymin, ymax + 1):
                    if dimension == 1 and y != 0: # we need not draw in this case
                        continue
                    for n in range(len(nodes)):
                        if nodes[n] in hidden_nodes:
                            continue

                        #print("apbara", conf.display_str(), x, y, nodes[n])
                        if Noneish(conf[(x, y), nodes[n]]):
                            continue
                        for t in topology:
                            a, b = t[1], t[2]
                            if a[-1] in hidden_nodes:
                                continue
                            if a[-1] == nodes[n]:
                                (xx, yy), nn = (vadd((x, y), vsub(b[:-1], a[:-1])), b[2])
                                #print(xx,yy,nn,nodes,conf)
                                if not Noneish(conf[(xx, yy), nn]):
                                    p = vadd(to_screen(x, y), vmul(zoom, nodeoffsets[nodes[n]]))
                                    #pp = to_screen(*vadd((xx, yy), nodeoffsets[nn]))
                                    pp = vadd(to_screen(xx, yy), vmul(zoom, nodeoffsets[nn]))
                                    pygame.draw.line(screen, GRAY, cp_to_screen(p), cp_to_screen(pp), 1)
                                
        # Draw the nodes, draw nodes, draw_nodes
        for x in range(xmin, xmax + 1):
            for y in range(ymin, ymax + 1):
                if dimension == 1 and y != 0:
                    continue
                for n in range(len(nodes)):
                    if nodes[n] in hidden_nodes:
                        continue
                    p = vadd(to_screen(x, y), vmul(zoom, nodeoffsets[nodes[n]]))
                    # highlight selected nodes and nodes currently being selected
                    if ((x,y),nodes[n]) in selection:
                        if ((x,y),nodes[n]) in backend.selection():
                            pygame.draw.circle(screen, GREEN, cp_to_screen(p), nodesize+6)
                        else:
                            pygame.draw.circle(screen, YELLOW, cp_to_screen(p), nodesize+6)
                    elif ((x,y),nodes[n]) in backend.selection():
                        pygame.draw.circle(screen, BLUE, cp_to_screen(p), nodesize+6)
                        
                    if Noneish(conf[(x,y),nodes[n]]):
                        continue
                    else:

                        #if grid[(x,y,n)] != UNKNOWN:
                        #    print (grid[(x,y,n)],  DEDUCED)

                        white_circle = False
                        #print(grid[(x,y,n)] )
                        #print("seeing", conf[x,y,nodes[n]], "at", (x,y,nodes[n]))
                        if isinstance(conf, RecognizableConf):
                            sym, fixed = conf[(x,y),nodes[n]]
                        elif isinstance(conf, AutomaticConf):
                            sym = conf[(x,y),nodes[n]]
                            fixed = False
                        #print(sym, fixed)
                        if type(sym) == list:
                            color = UNKNOWN_COLOR
                        #else:
                        #    print(grid[(x,y,n)], "!=", UNKNOWN)
                        else:
                            #sym_ix = sym # ???
                            #print(alphabets, nodes[n], sym, colors)
                            #sym = alphabets[nodes[n]][symidx]
                            #print(sym)
                            #color = colors[grid[(x,y,nodes[n])][1]]
                            try:
                                color = colors[nodes[n], sym]
                            except:
                                color = WHITE
                            white_circle = fixed

                        #if (x, y, n) in vemmel:
                        #    xxxx = int(255- gimmel[(x, y, nodes[n])]*3)
                        #    if xxxx < 0:
                        #        xxxx = 0
                        #    color = (0,0,xxxx)
                        #if (x, y, n) == gimmel[0]:
                            #print("did")
                        #    color = (60,70,80)
                        #print(gimmel, nnn) #time.time())

                        if white_circle:
                            pygame.draw.circle(screen, WHITE, cp_to_screen(p), nodesize+4)
                            pygame.draw.circle(screen, BLACK, cp_to_screen(p), nodesize+2)

                        drawing_picture = False
                        if pictures != None and nodes[n] in pictures:
                            drawing_picture = True

                        if not drawing_picture or True: # actually I like the circles
                            pygame.draw.circle(screen, color, cp_to_screen(p), nodesize)

                        if show_labels and not drawing_picture and sym != None and type(sym) != list:
                            #print(sym, color)
                            col = (255, 255, 255)
                            if sum(color) > 250:
                                col = (10, 10, 10)
                            
                            # write name of node, or draw picture
                            if pictures == None or nodes[n] not in pictures:
                                #print("rendering", sym)
                                font_surf = my_font.render(str(sym), False, col)
                                v = (font_surf.get_width()//2, -font_surf.get_height()//2)
                                screen.blit(font_surf, cp_to_screen(vsub(p, v)))
                                
                        if sym != None and type(sym) != list and drawing_picture:
                            #print("using pic", n, nodes, sym, pictures)
                            pic = pictures[nodes[n]][sym]
                            pic = pygame.transform.scale(pic, (nodesize*2, nodesize*2))
                            v = (pic.get_width()//2, -pic.get_height()//2)
                            screen.blit(pic, cp_to_screen(vsub(p, v)))

        
        # draw markers
    
        def draw_axis(q, xory, color, width):
            if xory == 0:
                a = (to_screen(q-0.5, 0)[0], 0)
                b = (a[0], screenheight)
                pygame.draw.line(screen, color, cp_to_screen(a), cp_to_screen(b), width)
            else:
                a = (0, to_screen(0, q-0.5)[1])
                b = (screenwidth, a[1])
                pygame.draw.line(screen, color, cp_to_screen(a), cp_to_screen(b), width)
                
        if show_markers:
            #if nnn%100 == 0: print("markers")
            for (i, marker) in enumerate(conf.markers):
                # x axis marker
                #if nnn%100 == 0: print(i, marker)
                for (j,q) in enumerate(marker):
                    width = 1
                    if j in [1, 2]:
                        width = 3
                    draw_axis(q, i, GREEN, width)
                if marker[0] == marker[1]:
                    draw_axis(marker[0], i, BLUE, 3)
                if marker[2] == marker[3]:
                    draw_axis(marker[2], i, BLUE, 3)
                    
            # draw moving markers
            if moving_marker is not None:
                # x axis marker
                #if nnn%100 == 0: print(i, marker)
                axis, marker = moving_marker
                for (j,q) in enumerate(marker):
                    draw_axis(q, axis, WHITE, 1)
                    
        
                               
        
        # Draw some helper text
        if cursor_state == CursorState.PAINT:
            if type(drawcolor) == tuple and drawcolor[0] == SET:
                draw_msg = ["Painting symbol {}".format(drawcolor[1])]
            elif drawcolor == FIXITY:
                draw_msg = ["Painting {} {}".format(drawcolor, paint_fixity)]
            else:
                draw_msg = ["Painting {}".format(drawcolor)]
        elif cursor_state == CursorState.MOVE_MARKERS:
            if moving_marker is None:
                draw_msg = ["Select marker to move"]
            else:
                axis, markers = moving_marker
                draw_msg = ["Place {} {} marker".format(["1st","2nd","3rd","4th"][len(markers)], ["vertical","horizontal"][axis])]
        else:
            raise Exception("Unknown cursor state: {}".format(cursor_state))
        draw_msg.append("x-axis state: %s" % backend.axis_states[0])
        if dim == 2:
            draw_msg.append("y-axis state: %s" % backend.axis_states[1])
        if show_help:
            draw_msg.append("")
            draw_msg.append("Select nodes: right mouse button")

            draw_msg.append("Pick symbol: number keys")
            draw_msg.append("Pick <unknown symbol>: u")
            draw_msg.append("Pick <erase node>: backspace")
            draw_msg.append("Pick <fixity>: f")

            draw_msg.append("Pan: arrow keys")
            draw_msg.append("Zoom: az")
            if not linknodesizeandzoom:
                draw_msg.append("Node size: sx")
            draw_msg.append("Toggle axis states: cv")
            draw_msg.append("Toggle cursor state: d")
            draw_msg.append("Deduce pattern: spacebar")
            draw_msg.append("Clear deduced nodes: e")
            draw_msg.append("Clear all nodes: shift-e")
            draw_msg.append("Set all nodes to unknown: shift-ctrl-e")
            draw_msg.append("Remove all nodes: shift-backspace")
            draw_msg.append("Minimize markers: m")
            draw_msg.append("Toggle (showing) markers: ctrl+m")
            draw_msg.append("Copy selection: ctrl-c")
            draw_msg.append("Paste selection: ctrl-v")
            draw_msg.append("Undo: ctrl-z")
            draw_msg.append("Redo: ctrl-y")
            draw_msg.append("Toggle grid lines: ctrl-h")
            #draw_msg.append("Cancel deduction: escape")
            draw_msg.append("Toggle symbol labels: l")
            draw_msg.append("Toggle UI: h")
     
            #screen.blit(textinput.surface, (30, 30))
            manager.draw_ui(screen)

        
        for (i, msg) in enumerate(draw_msg):
            font_surf = msg_font.render(msg, False, GREEN, BLACK)
            screen.blit(font_surf, (10, 10+i*15))

        # Limit to 60 frames per second
        clock.tick(60)
     
        # Go ahead and update the screen with what we've drawn.
        pygame.display.flip()
     
    # Be IDLE friendly. If you forget this line, the program will 'hang'
    # on exit.
    pygame.quit()
