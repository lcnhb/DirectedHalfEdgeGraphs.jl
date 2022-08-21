module TestDirectedHalfEdgeGraphs
using DirectedHalfEdgeGraphs

using Test
using Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs
using Catlab.Graphs.GraphGenerators
using Catlab.Graphs
using Catlab.Theories

@testset "constructing" begin
gh =DirectedHalfEdgeGraph(6)
add_edges!(gh, [1,1,1,2,2,4,4,5,6],[2,5,3,5,4,6,3,6,5] )
@test sink(gh,[1,1,1,2,2,4,4,5,6])==falses(9)
@test source(gh,[2,5,3,5,4,6,3,6,5])==trues(9)
@test add_dangling_edges!(gh, [1,2,3,4],dirs=[true,false,true,false])==19:22

@test connected_components(gh⊕gh)==[[1, 2, 3, 4, 5, 6],[7, 8, 9, 10, 11, 12]]

@test add_half_edge_pairs!(gh, [1,2,3], [2,3,1])==23:28
@test half_edges(gh)==1:28
@test incident(gh,2,:vertex)==[4, 5, 10, 20, 24, 26]

spanningTree=subtree(gh,dfs_parents(gh,1,all_neighbors))

using DirectedHalfEdgeGraphs: to_graphviz_property_graph,fixinv!
using StatsBase

edges(spanningTree|>hom|>dom)
countmap(zip(edges(spanningTree|>hom|>dom)...))
tree(dfs_parents(gh,1,all_neighbors))
parents=dfs_parents(gh⊕gh,12,all_neighbors)


subgraph=subtree(gh⊕gh,dfs_parents(gh⊕gh,6,all_neighbors))

gh
spanningTree|>hom|>dom
to_graphviz(gh)
to_graphviz(gh⊕gh)
to_graphviz(spanningTree)
to_graphviz(subgraph)
end



end