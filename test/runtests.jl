module TestDirectedHalfEdgeGraphs
using DirectedHalfEdgeGraphs

using Test
using Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs
using Catlab.Graphs.GraphGenerators
using Catlab.Graphs
using Catlab.Theories

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
canonical_hash(gh)
nickel_index(call_nauty(gh).cset)
gh



using Catlab.Graphs, Catlab.CategoricalAlgebra, Catlab.Programs
SchDirectedHalfEdgeGraph
simp = @migration SchDirectedHalfEdgeGraph SchHalfEdgeGraph  begin
  V => V
  H => H
  inv => inv
  Truth => @cases begin end 
end
@migration SchSymmetricGraph SchHalfEdgeGraph begin
  V => V
  E => H
  src => vertex
  tgt => compose(inv, vertex)
  inv => inv
end

@migration  SchGraph SchWeightedGraph begin
  V => V
  E => E
  Weight => @empty
end

test=@migration SchGraph SchWeightedGraph begin
  V => V
  E => E
  src => src
  tgt => tgt
 end

 g = WeightedGraph{Float64}(4)
 add_edges!(g, 1:3, 2:4, weight=[0.25, 0.5, 0.75])
g


migrate(Graph,g,test)
simp(gh)
@testset "constructing" begin
end

simp = @migration SchHalfEdgeGraph SchDirectedHalfEdgeGraph begin
  V => V
  H => H
  inv => inv
  vertex => vertex
end

F = @migration SchGraph SchGraph begin
  V => V
  E => @join begin
    v::V
    (e₁, e₂)::E
    (e₁ → v)::tgt
    (e₂ → v)::src
  end
  src => e₁ ⋅ src
  tgt => e₂ ⋅ tgt
end
@test F isa DataMigrations.ConjSchemaMigration
F_E = diagram(ob_map(F, :E))
to_graphviz(F_E)

end