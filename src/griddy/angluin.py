
from general import words
from finite_automata import DFA

# Learn a DFA with output from evaluation and equivalence queries with backtracking
# Extension of Angluin's algorithm L*
# https://www.sciencedirect.com/science/article/pii/0890540187900526
# There is a learner process and a teacher process
# The learner process can ask the teacher "what is the output for word w" (evaluation) and "is this DFA correct" (equivalence)
# To an incorrect equivalence query the teacher must give a counterexample
# The teacher is, at any point, allowed to backtrack some evaluations
# This means it can say "evaluations of words w1, ..., wk that I gave earlier are possibly incorrect, ignore them"

class BacktrackException(Exception):
    def __init__(self, data):
        super().__init__("Backtrack now")
        self.data = data

class DFALearner:

    def __init__(self, input_alph):
        self.input_alph = input_alph
        self.state_words = [tuple()]
        self.sep_words = [tuple()]
        self.output_table = dict()
        # History is tagged
        # The current state is generally different from the last saved one
        self.history = []
        self.eval_count = 0
        self.eq_count = 0
        self.total_eval_count = 0
        self.total_eq_count = 0

    def store(self, tag):
        "Store the current state in the history list"
        self.history.append((tag, self.state_words, self.sep_words, self.output_table, self.eval_count, self.eq_count))
        self.state_words = self.state_words.copy()
        self.sep_words = self.sep_words.copy()
        self.output_table = self.output_table.copy()


    def recall(self, tag):
        "Backtrack to the moment before we stored tag t"
        # Tag t corresponds to the state right *before* we asked an eval query and the response was tagged with t
        # Hence, if we have to backtrack that evaluation, we should
        # 1) recall the state tagged with t and
        # 2) forget recent history up to *and including* tag t
        # Then our next move will be to ask the same eval query
        i = 0
        while i < len(self.history):
            the_tag, state_words, sep_words, output_table, eval_count, eq_count = self.history[i]
            if the_tag == tag:
                break
            i += 1
        else:
            return
        self.state_words = state_words
        self.sep_words = sep_words
        self.output_table = output_table
        self.eval_count = eval_count
        self.eq_count = eq_count
        self.history = self.history[:i]

    def learn(self):
        """
        A generator for the learning process.
        It generates query values ("eval", w) and ("eq", X) where w is a word and X is a DFA.
        The teacher must answer with ("out", o) for the first,
        and either ("yes", None) or ("no", w) to the second.
        Both queries can be answered with ("backtrack", [w1, ..., wk]).
        """

        while True:
            try:
                for e in self.sep_words:
                    for w in self.state_words:
                        w2 = w + e
                        if w2 not in self.output_table:
                            self.eval_count += 1
                            self.total_eval_count += 1
                            (msg, data, tag) = yield ("eval", w2)
                            if msg == "val":
                                self.store(tag)
                                self.output_table[w2] = data
                            else:
                                raise BacktrackException(data)
                        for a in self.input_alph:
                            w2 = w + (a,) + e
                            if w2 not in self.output_table:
                                self.eval_count += 1
                                self.total_eval_count += 1
                                (msg, data, tag) = yield ("eval", w2)
                                if msg == "val":
                                    self.store(tag)
                                    self.output_table[w2] = data
                                else:
                                    raise BacktrackException(data)
                change = self.make_consistent()
                if change:
                    continue
                change = self.close()
                if change:
                    continue
                dfa = self.make_dfa()
                self.eq_count += 1
                self.total_eq_count += 1
                (msg, data, _) = yield ("eq", dfa)
                if msg == "yes":
                    # Success
                    return
                elif msg == "no":
                    # Counterexample
                    # print("Counterexample", data)
                    #i = max(i for i in range(len(data)+1) if data[:i] in self.state_words)
                    #for j in range(i, len(data)+1):
                    #    if data[j:] not in self.sep_words:
                    #        self.sep_words.append(data[j:])
                    for i in range(len(data)+1):
                        if data[:i] not in self.state_words:
                            self.state_words.append(data[:i])
                else:
                    # Backtrack
                    raise BacktrackException(data)
            except BacktrackException as e:
                #print("Backtracking with", e.data, [p[0] for p in self.history])
                #1/0
                for tag in e.data:
                    self.recall(tag)
            

    def make_consistent(self):
        "Make the output table more consistent, return whether changes were made"
        # Assert complete
        for w1 in self.state_words:
            for w2 in self.state_words:
                if self.row(w1) == self.row(w2):
                    for a in self.input_alph:
                        for e in self.sep_words:
                            if self.output_table[w1 + (a,) + e] != self.output_table[w2 + (a,) + e]:
                                self.sep_words.append((a,) + e)
                                return True
        return False
                        
    def close(self):
        "Make the output table more closed, return whether changes were made"
        # Assert complete
        for w1 in self.state_words:
            for a in self.input_alph:
                the_row = self.row(w1 + (a,))
                for w2 in self.state_words:
                    if self.row(w2) == the_row:
                        break
                else:
                    self.state_words.append(w1 + (a,))
                    return True
        return False

    def make_dfa(self):
        "Return the DFA associated to the output table"
        # Assert complete, closed and consistent
        outputs = dict()
        trans = dict()
        for w in self.state_words:
            the_row = self.row(w)
            outputs[the_row] = self.output_table[w]
            for a in self.input_alph:
                trans[the_row, a] = self.row(w + (a,))
        dfa = DFA(self.input_alph, trans, self.row(tuple()), outputs=outputs)
        dfa.rename()
        return dfa

    def row(self, w):
        "Compute row of state word or state word plus symbol"
        # Assert complete
        return tuple(self.output_table[w+e] for e in self.sep_words)


# Gold's algorithm: infer a DFA from given outputs for all words up to length k

def infer_dfa(alph, word_outputs):
    "Given a dict of word : output containing all words up to length k, infer a DFA."
    # merges[w] points to the earliest word that w has been merged with
    #print("inferring", alph, word_outputs)
    if len(word_outputs) == 1:
        # singleton, special case
        return DFA(alph, {(0, sym): 0 for sym in alph}, 0, outputs={0 : min(word_outputs.values())})
    merges = dict()
    states = []
    for (word, out) in sorted(word_outputs.items(), key=lambda p: (len(p[0]), p)):
        #print("processing", word, out)
        for st_word in states:
            if consistent(word, st_word, alph, word_outputs, merges):
                # found not-inequivalent processed state, merge them
                #print("merging with", st_word)
                merges[word] = st_word
                break
        else:
            # no mergable processed state
            states.append(word)
            merges[word] = word

    # create transition table
    trans = dict()
    for word in states:
        for sym in alph:
            if word + (sym,) in merges:
                trans[word, sym] = merges[word + (sym,)]
            else:
                # find a not-inequivalent state and use it
                for st in states:
                    if consistent(st, word + (sym,), alph, word_outputs, merges):
                        trans[word, sym] = st
                        break
                else:
                    raise Exception("No mergable state (this should not happen)")
    outputs = {word : word_outputs[word]
               for word in states}
    dfa = DFA(alph, trans, (), outputs=outputs)
    dfa.rename()
    return dfa
    

def consistent(st1, st2, alph, outputs, merges, seen=None):
    "Do all words lead into equivalent states (or nothing)?"
    if seen is None:
        seen = set()
    if (st1, st2) in seen or st1 not in outputs or st2 not in outputs:
        return True
    if outputs[st1] != outputs[st2]:
        return False
    seen.add((st1, st2))
    for sym in alph:
        new_st1 = st1 + (sym,)
        if new_st1 in merges:
            new_st1 = merges[st1]
        new_st2 = st2 + (sym,)
        if new_st2 in merges:
            new_st2 = merges[new_st2]
        if not consistent(new_st1, new_st2, alph, outputs, merges, seen=seen):
            return False
    return True

def test_angluin():
    # Let's test with words that begin and end with 01
    f = lambda w: len(w) >= 2 and w[:2] == (0,1) and w[-2:] == (0,1)
    counterexamples = [(0,1),(1,0,1)]
    L = DFALearner([0,1])
    p = L.learn()
    print("learning")
    (msg, data) = next(p)
    while True:
        print("teacher got", msg, data)
        if msg == "eval":
            print("teacher sending", "val", f(data))
            (msg, data) = p.send(("val", f(data)))
        elif msg == "eq":
            print(data.info_string(verbose=True))
            if counterexamples:
                sent = ("no", counterexamples.pop(0))
                print("teacher sending", sent)
                (msg, data) = p.send(sent)
            else:
                break
    # Let's test with backtracking: we first make an error with (1,1) -> True, then correct it after 10 rounds
    print()
    counterexamples = [(0,1),(0,0,0,1)]
    error_made = False
    counter = -1 # steps to correct error
    wrong = (1,1)
    L = DFALearner([0,1])
    p = L.learn()
    print("learning")
    (msg, data) = next(p)
    while True:
        counter -= 1
        print("teacher got", msg, data)
        if counter == 0:
            print("teacher sending", "backtrack", [wrong], "!!!!!!!!")
            (msg, data) = p.send(("backtrack", [wrong]))
        elif msg == "eval":
            if data == wrong and not error_made:
                val = not f(data)
                error_made = True
                counter = 10
                print("hehe")
            else:
                val = f(data)
            print("teacher sending", "val", val)
            (msg, data) = p.send(("val", val))
        elif msg == "eq":
            print(data.info_string(verbose=True))
            if counterexamples:
                sent = ("no", counterexamples.pop(0))
                print("teacher sending", sent)
                (msg, data) = p.send(sent)
            else:
                break

def test_gold():
    alph = [0,1]
    word_outputs = {word : sum(1 for i in range(len(word)) if word[i:i+2] == (1,1))%3
                    for k in range(6)
                    for word in words(k, alph)}
    dfa = infer_dfa(alph, word_outputs)
    print(dfa.info_string(verbose=True))

if __name__ == "__main__":
    test_gold()
