module TestDirectedHalfEdgeGraphs
using DirectedHalfEdgeGraphs
using Test
using Catlab.CategoricalAlgebra.CSets


gh = @acset DirectedHalfEdgeGraph begin
    V = 4
    H = 7
    vertex=[1,2,3,4,1,2,3]
    inv=[2,1,3,5,4,7,6]
    sink=[1,1,0,1,0,1,0].>0
  end
  
add_edges!(gh, [1,2,3], [2,3,1])
add_dangling_edges!(gh, [1,1,3],dirs=[true,false,true])
half_edges(gh)
subpart(gh,:inv)
incident(gh,2,:vertex)
to_graphviz(gh)


@testset "DirectedHalfEdgeGraphs.jl" begin
    # Write your tests here.
    gh = @acset DirectedHalfEdgeGraph begin
        V = 4
        H = 7
        vertex=[1,2,3,4,1,2,3]
        inv=[2,1,3,5,4,7,6]
        sink=[1,1,0,1,0,1,0].>0
      end
      
      add_edges!(gh, [1,2,3], [2,3,1])
      add_dangling_edges!(gh, [1,1,3],dirs=[true,false,true])
      half_edges(gh)
      subpart(gh,:inv)
      incident(gh,2,:vertex)
      to_graphviz(gh)
      
end
end