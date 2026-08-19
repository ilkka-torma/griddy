# Node automorphisms: bijections from the set of all nodes to itself that approximately preserve distances
# Examples include rotations, reflections and translations
# Can be applied to nodes obviously, but also to circuits, clopen sets, SFTs, and block maps (by conjugation)
# Can be analyzed at least for periodicity and whether they leave something invariant
# Can be used to force symmetries in SFTs, block maps, discharging arguments etc

from general import *
import circuit
import sft
import blockmap
import numpy

class NodeAutomorphism:
    "The abstract class for node automorphisms."

    pass

class AffineAutomorphism:
    "An affine node automorphism on Z^d: each node (v; r) is mapped to (A v+c_r; r')."

    def __init__(self, dim=None, nodes=None, node_map=None, matrix=None, vectors=None):
        #print("making aut", matrix, vectors, node_map)
        self.dim = dim
        if nodes is None:
            if node_map is not None:
                self.nodes = list(node_map)
            else:
                self.nodes = sft.Nodes()
        else:
            self.nodes = nodes
        if node_map is None:
            self.node_map = {node : node for node in self.nodes}
        else:
            self.node_map = node_map
        if not (set(self.nodes) == set(self.node_map) == set(self.node_map.values())):
            raise GriddyRuntimeError("Affine node automorphism needs bijection on nodes")
        self.inv_node_map = {self.node_map[node] : node for node in self.nodes}
        if dim is None:
            # deduce dim from matrix or vectors
            if matrix is not None:
                dim = len(matrix)
            elif vectors is not None:
                dim = len(next(vectors.values()))
            else:
                raise GriddyRuntimeError("Could not deduce dimension of affine automorphism")
        self.dim = dim
        if matrix is None:
            self.matrix = numpy.identity(dim).astype(int)
        else:
            self.matrix = numpy.array(matrix)
        if abs(numpy.linalg.det(self.matrix)) != 1:
            raise GriddyRuntimeError("Affine node automorphism needs matrix of determinant 1 or -1")
        self.inv_matrix = numpy.linalg.inv(self.matrix).astype(int)
        if vectors is None:
            self.vectors = {node : numpy.zeros((dim, 1)).astype(int)
                            for node in self.nodes}
        else:
            self.vectors = {node :
                            numpy.array([[i] for i in vec]).astype(int)
                            if type(vec) == tuple
                            else vec
                            for (node, vec) in vectors.items()}
        self._hash = hash((tuple(self.matrix.flat), tuple((node, tuple(vec.flat)) for (node, vec) in self.vectors.items()), tuple(self.node_map.items())))
        #print("made", self.matrix, self.vectors, self.node_map)

    @classmethod
    def from_examples(self, examples, nodes=None):
        "Produce a node automorphism from finitely many examples."
        # deduce node map
        seen_nodes = set(nvec[1] for pair in examples.items() for nvec in pair)
        if nodes is None:
            nodes = list(seen_nodes)
        else:
            nodes = list(nodes)
        node_map = {nvec[1] : img[1] for (nvec, img) in examples.items()}
        missing_node = None
        missing_img = None
        for node in seen_nodes:
            if node not in node_map:
                missing_node = node
            if node not in node_map.values():
                missing_img = node
        if missing_node is not None:
            node_map[missing_node] = missing_img
        for node in nodes:
            if node not in node_map:
                node_map[node] = node

        # deduce matrix and vectors by solving a system of linear equations
        dim = len(list(examples)[0][0])
        examples = list(examples.items())
        coeff_matrix = []
        res_vector = []
        for ((vec, node), (img_vec, _)) in examples:
            for j in range(dim):
                coeff_matrix.append(
                    [(i==j)*vec[k] for i in range(dim) for k in range(dim)] +\
                    [(i==j)*int(n==node) for n in nodes for i in range(dim)])
                res_vector.append(img_vec[j])
        if len(coeff_matrix) < len(coeff_matrix[0]):
            raise GriddyRuntimeError("Could not deduce affine automorphism: underdetermined")
        #print("dim", dim, "nodes", nodes, "matrix", coeff_matrix, "vec", res_vector)
        try:
            res = numpy.linalg.lstsq(numpy.array(coeff_matrix), numpy.array(res_vector))
        except numpy.linalg.LinAlgError:
            raise GriddyRuntimeError("Could not deduce affine automorphism: unsolvable")
        res2 = []
        for x in res[0]:
            y = int(round(x))
            if not (-0.000002 <= x-y <= 0.000002):
                raise GriddyRuntimeError("Could not deduce affine automorphism: non-integer solution")
            res2.append(y)
        matrix = [res2[i*dim:(i+1)*dim]
                  for i in range(dim)]
        vectors = {node : tuple(res2[dim*dim+i*dim:dim*dim+(i+1)*dim])
                   for (i, node) in enumerate(nodes)}
        aut = self(dim=dim, nodes=nodes, matrix=matrix, vectors=vectors, node_map=node_map)

        # check that aut agrees with examples
        for (nvec, img) in examples:
            if aut(nvec) != img:
                raise GriddyRuntimeError("Could not deduce affine automorphism: invalid solution ({} -> {} != {})".format(nvec, aut(nvec), img))
        return aut

    def __hash__(self):
        return self._hash

    def __repr__(self):
        return "AffineAutomorphism(node_map={}, matrix={}, vectors={})".format(self.node_map, self.matrix, self.vectors)

    def __eq__(self, other):
        if isinstance(other, AffineAutomorphism):
            return self.dim == other.dim and\
                self.node_map == other.node_map and\
                numpy.array_equal(self.matrix, other.matrix) and\
                all(numpy.array_equal(self.vectors[node], other.vectors[node])
                    for node in self.nodes)
        else:
            return False

    def __call__(self, arg, inv=False):
        "Apply the automorphism to a value, whose type is inferred at runtime."
        #print("call", arg)
        if type(arg) == tuple and len(arg) in [2,3]:
            # node vector
            vec, node = arg[:2]
            vecmat = numpy.asmatrix([[i] for i in vec])
            if inv:
                new_node = self.inv_node_map[node]
                new_vec = self.inv_matrix @ (vecmat - self.vectors[new_node])
                ret = (tuple(int(x) for x in new_vec.flat), new_node) + arg[2:]
            else:
                new_vec = self.matrix @ vecmat + self.vectors[node]
                ret = (tuple(int(x) for x in new_vec.flat), self.node_map[node]) + arg[2:]
        elif isinstance(arg, circuit.Circuit):
            circ = arg.copy()
            circuit.transform(circ, lambda var: self(var))
            ret = circ
        elif isinstance(arg, sft.SFT):
            # TODO: transform topology?
            if arg.onesided:
                raise GriddyRuntimeError("Cannot transform SFT with onesided directions")
            ret = sft.SFT(arg.dim, arg.nodes, arg.alph, arg.topology, arg.graph, circuit=self(arg.circuit))
        elif isinstance(arg, sft.Clopen):
            # TODO: transform topology?
            if arg.onesided:
                raise GriddyRuntimeError("Cannot transform clopen set with onesided directions")
            ret = sft.Clopen(arg.dim, arg.nodes, arg.alph, arg.topology, arg.graph, circuit=self(arg.circuit))
        elif isinstance(arg, sft.CSIntersection):
            # TODO: transform topology?
            if arg.onesided:
                raise GriddyRuntimeError("Cannot transform set with onesided directions")
            ret = sft.CSIntersection(sft=self(arg.sft), clopen=self(arg.clopen))
        else:
            raise GriddyRuntimeError("Could not apply affine automorphism to {}".format(type(arg)))
        # TODO: add configurations and block maps
        #print("ret", ret)
        return ret

    def then(self, other):
        "Compose affine automorphisms."
        comp_node_map = {node : other.node_map[self.node_map[node]]
                         for node in self.nodes}
        comp_matrix = other.matrix @ self.matrix
        comp_vectors = {node : other.matrix @ self.vectors[node] + other.vectors[img_node]
                        for (node, img_node) in self.node_map.items()}
        return AffineAutomorphism(node_map=comp_node_map, matrix=comp_matrix, vectors=comp_vectors)

    def shift_to_map(self, source, target=None):
        """
            Compose with a translation to map source nvec to target nvec.
            Missing target means target=source.
            Return a new automorphism, or None if not possible.
        """
        if target is None:
            target = source
        img_vec, img_node = self(source)
        if img_node != target[1]:
            return None
        tr_vec = numpy.array([[i] for i in vsub(target[0], img_vec)]).astype(int)
        new_vecs = {node : vec + tr_vec for (node, vec) in self.vectors.items()}
        ret = AffineAutomorphism(
            dim=self.dim, nodes=self.nodes, node_map=self.node_map, matrix=self.matrix,
            vectors=new_vecs)
        assert ret(source) == target
        return ret

    @classmethod
    def generate_group(self, generators, dim=None, nodes=None):
        "The symmetry group generated by the given automorphisms. Hangs if the group is infinite."
        if not generators:
            # trivial group
            return [AffineAutomorphism(dim=dim, nodes=nodes)]
        dim = generators[0].dim
        nodes = generators[0].nodes
        frontier = list(generators)
        identity = AffineAutomorphism(dim=dim, nodes=nodes)
        group = list(frontier)
        if identity not in group:
            group = [identity] + group
        while frontier:
            new_frontier = []
            for elem in frontier:
                for gen in generators:
                    new_elem = elem.then(gen)
                    if new_elem not in group:
                        group.append(new_elem)
                        new_frontier.append(new_elem)
            frontier = new_frontier
        return group
