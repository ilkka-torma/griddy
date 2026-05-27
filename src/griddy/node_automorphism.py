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
            self.matrix = numpy.identity(dim)
        else:
            self.matrix = numpy.asmatrix(matrix)
        if abs(numpy.linalg.det(self.matrix)) != 1:
            raise GriddyRuntimeError("Affine node automorphism needs matrix of determinant 1 or -1")
        self.inv_matrix = numpy.linalg.inv(self.matrix).astype(int)
        if vectors is None:
            self.vectors = {node : numpy.zeros((dim, 1)) for node in self.nodes}
        else:
            self.vectors = {node : numpy.array(vec) for (node, vec) in vectors.items()}

    def __repr__(self):
        return "AffineAutomorphism(node_map={}, matrix={}, vectors={})".format(self.node_map, self.matrix, self.vectors)

    def __call__(self, arg, inv=False):
        "Apply the automorphism to a value, whose type is inferred at runtime."
        #print("call", arg)
        if type(arg) == tuple and len(arg) in [2,3]:
            # node vector
            vec, node = arg[:2]
            if inv:
                new_node = self.inv_node_map[node]
                new_vec = numpy.matvec(self.inv_matrix, vec - self.vectors[new_node])
                return (tuple(int(x) for x in new_vec.flat), new_node) + arg[2:]
            else:
                new_vec = numpy.matvec(self.matrix, vec) + self.vectors[node]
                return (tuple(int(x) for x in new_vec.flat), self.node_map[node]) + arg[2:]
        elif isinstance(arg, circuit.Circuit):
            circ = arg.copy()
            circuit.transform(circ, lambda var: self(var))
            return circ
        elif isinstance(arg, sft.SFT):
            # TODO: transform topology?
            if arg.onesided:
                raise GriddyRuntimeError("Cannot transform SFT with onesided directions")
            return sft.SFT(arg.dim, arg.nodes, arg.alph, arg.topology, arg.graph, circuit=self(arg.circuit))
        elif isinstance(arg, sft.Clopen):
            # TODO: transform topology?
            if arg.onesided:
                raise GriddyRuntimeError("Cannot transform clopen set with onesided directions")
            return sft.Clopen(arg.dim, arg.nodes, arg.alph, arg.topology, arg.graph, circuit=self(arg.circuit))
        elif isinstance(arg, sft.CSIntersection):
            # TODO: transform topology?
            if arg.onesided:
                raise GriddyRuntimeError("Cannot transform set with onesided directions")
            return sft.CSIntersection(sft=self(arg.sft), clopen=self(arg.clopen))
        else:
            raise GriddyRuntimeError("Could not apply affine automorphism to {}".format(type(arg)))
        # TODO: add configurations and block maps

