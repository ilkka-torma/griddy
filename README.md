# Griddy
Griddy (GRaphs and Infinite Discrete DYnamical systems): a Python toolbox for analysis of infinite graphs and infinite discrete dynamical systems.
Griddy includes a domain-specific language for defining and analyzing
* multidimensional shifts of finite type,
* multidimensional sliding block codes (including cellular automata),
* one-dimensional sofic shifts,
* and more,
using expressive logical formulas.
For example, one can easily define the set of 2-vertex covers on the infinite square grid and compute its minimum density.

```
-- The default graph structure is the two-dimensional square grid
-- The default alphabet is {0, 1}
-- Define the set of 2-vertex covers:
%sft two_vertex_cover
  Ap      -- for all nodes p
  #q[p:1] -- the number of nodes q in the 1-ball around p
  q=1     -- that contain the value 1 (are in the cover)
  >= 2    -- is at least 2
   
-- Compute a lower bound of 0.4 for the density of 1-symbols
%density_lower_bound two_vertex_cover (0,1) (1,0); (0,1) (1,0) (0,-1) (-1,0) (1,1) (-1,-1) (1,-1)

-- Then reach that bound with a (0,5)-periodic configuration
%compute_forbidden_patterns two_vertex_cover
%minimum_density conf_name=c two_vertex_cover (0,5)

-- View the extremal configuration in tiler
%tiler two_vertex_cover initial=c
```

See the [examples folder](https://github.com/ilkka-torma/griddy/tree/main/examples) for more examples and the [wiki](https://github.com/ilkka-torma/griddy/wiki) for documentation.
