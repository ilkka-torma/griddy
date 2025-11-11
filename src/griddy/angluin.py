# Learn a DFA with output from evaluation and equivalence queries with backtracking
# Extension of Angluin's algorithm L*
# https://www.sciencedirect.com/science/article/pii/0890540187900526
# There is a learner process and a teacher process
# The learner process can ask the teacher "what is the output for word w" (evaluation) and "is this DFA correct" (equivalence)
# To an incorrect equivalence query the teacher must give a counterexample
# The teacher is, at any point, allowed to backtrack some evaluations
# This means it can say "evaluations of words w1, ..., wk that I gave earlier are possibly incorrect, ignore them"

from finite_automata import DFA

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
        self.history = []
        self.eval_count = 0
        self.eq_count = 0
        self.total_eval_count = 0
        self.total_eq_count = 0

    def store(self, tag):
        self.history.append((tag, self.state_words, self.sep_words, self.output_table, self.eval_count, self.eq_count))
        self.state_words = self.state_words.copy()
        self.sep_words = self.sep_words.copy()
        self.output_table = self.output_table.copy()


    def recall(self, tag):
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
                            (msg, data, tag) = yield ("eval", w2)
                            self.eval_count += 1
                            self.total_eval_count += 1
                            if msg == "val":
                                self.store(tag)
                                self.output_table[w2] = data
                            else:
                                raise BacktrackException(data)
                        for a in self.input_alph:
                            w2 = w + (a,) + e
                            if w2 not in self.output_table:
                                (msg, data, tag) = yield ("eval", w2)
                                self.eval_count += 1
                                self.total_eval_count += 1
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
                (msg, data, _) = yield ("eq", dfa)
                self.eq_count += 1
                self.total_eq_count += 1
                if msg == "yes":
                    # Success
                    return
                elif msg == "no":
                    # Counterexample
                    #print("Counterexample", data)
                    for i in range(len(data)+1):
                        if data[:i] not in self.state_words:
                            #print("Storing", data[:i])
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


def test():
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

if __name__ == "__main__":
    test()
