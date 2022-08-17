module DirectedHalfEdgeGraphs

export SchDirectedHalfEdgeGraph,AbstractDirectedHalfEdgeGraph,DirectedHalfEdgeGraph,sink,source,in_edges,out_edges,half_edge_pairs,add_half_edge_pairs!,add_dangling_edge!,add_dangling_edges!,to_graphviz,to_graphviz_property_graph,edges,dangling_edges

using Catlab
using Base: @invoke
using Catlab.CategoricalAlgebra.CSets,Catlab.Graphics,Catlab.Graphs,Catlab.Graphics.GraphvizGraphs

import Catlab.Graphs.BasicGraphs: add_dangling_edges!, add_dangling_edge!, half_edge_pairs,add_half_edge_pairs!
import Catlab.Graphics.GraphvizGraphs: to_graphviz, to_graphviz_property_graph

@present SchDirectedHalfEdgeGraph <: SchHalfEdgeGraph begin
  dir::AttrType
  sink::Attr(H, dir)

end

@abstract_acset_type AbstractDirectedHalfEdgeGraph <: AbstractHalfEdgeGraph


@acset_type DirectedHalfEdgeGraphGeneric(SchDirectedHalfEdgeGraph, index=[:inv, :vertex, :sink]) <: AbstractDirectedHalfEdgeGraph

DirectedHalfEdgeGraph=DirectedHalfEdgeGraphGeneric{Bool}

sink(g::AbstractDirectedHalfEdgeGraph, args...) = subpart(g, args..., :sink)
source(g::AbstractDirectedHalfEdgeGraph, args...) = .!subpart(g, args..., :sink)

""" Half-edges in a half-edge graph, or incident to a vertex.
"""
in_edges(g::AbstractDirectedHalfEdgeGraph) = half_edges(g)[sink(g)]

function in_edges(g::AbstractDirectedHalfEdgeGraph, v)
  edges = half_edges(g, v)
  filter = sink(g, edges)
  return edges[filter]
end


out_edges(g::AbstractDirectedHalfEdgeGraph) = half_edges(g)[source(g)]

function out_edges(g::AbstractDirectedHalfEdgeGraph, v)
  edges = half_edges(g, v)
  filter = source(g, edges)
  return edges[filter]
end

function edges(g::AbstractDirectedHalfEdgeGraph)
  H=half_edges(g)
  filter=inv(g,H).!=H
  return H[filter]
end


function half_edge_pairs(g::AbstractDirectedHalfEdgeGraph, src::Int, tgt::Int)
  out = out_edges(g, src)
  in = inv(g, out)
  has_tgt = vertex(g, in) .== tgt
  (out[has_tgt], in[has_tgt])
end

function half_edge_pairs(g::AbstractDirectedHalfEdgeGraph)
  out = out_edges(g)
  in = inv(g, out)
  is_inner = in .!= out
  (out[is_inner], in[is_inner])
end



function add_half_edge_pairs!(g::AbstractDirectedHalfEdgeGraph, srcs::AbstractVector{Int},
  tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  outs = add_parts!(g, :H, n; vertex=srcs, kw...)
  ins = add_parts!(g, :H, n; vertex=tgts, kw...)
  set_subpart!(g, outs, :inv, ins)
  set_subpart!(g, outs, :sink, falses(n))
  set_subpart!(g, ins, :inv, outs)
  set_subpart!(g, ins, :sink, trues(n))
  first(outs):last(ins)
end


""" Add a dangling edge to a half-edge graph.
A "dangling edge" is a half-edge that is paired with itself under the half-edge
involution. They are usually interpreted differently than "self-loops", i.e., a
pair of distinct half-edges incident to the same vertex.
"""

function add_dangling_edge!(g::AbstractDirectedHalfEdgeGraph, v::Int; dir=true, kw...)
  H=add_part!(g, :H; vertex=v, inv=nparts(g,:H)+1,sink=dir,kw...)
end

function add_dangling_edges!(g::AbstractDirectedHalfEdgeGraph, vs::AbstractVector{Int}; dirs::AbstractVector{Bool},kw...)
  n, k = length(vs), nparts(g, :H)
  H=add_parts!(g, :H, n; vertex=vs, inv=(k+1):(k+n),sink=dirs, kw...)
end

function dangling_edges(g::AbstractDirectedHalfEdgeGraph;incoming=true,outgoing=true)
  H=Int[]
  incoming && append!(H,in_edges(g))
  outgoing && append!(H,out_edges(g))
  is_dangling=inv(g,H).==H
  return H[is_dangling]
end

function dangling_edges(g::AbstractDirectedHalfEdgeGraph,v;incoming=true,outgoing=true)
  H=Int[]
  incoming && append!(H,in_edges(g,v))
  outgoing && append!(H,out_edges(g,v))
  is_dangling=inv(g,H).==H
  return H[is_dangling]
end
  

function default_node_attrs(labels::Union{Symbol,Bool})
  shape = labels isa Symbol ? "ellipse" : (labels ? "circle" : "point")
  Dict(:shape => shape, :width => "0.05", :height => "0.05", :margin => "0")
end
node_label(g, name::Symbol, v::Int) = Dict(:label => string(g[v, name]))
node_label(g, labels::Bool, v::Int) = Dict(:label => labels ? string(v) : "")

edge_label(g, name::Symbol, e::Int) = Dict(:label => string(g[e, name]))
edge_label(g, labels::Bool, e::Int) =
  labels ? Dict(:label => string(e)) : Dict{Symbol,String}()

to_graphviz(g::AbstractDirectedHalfEdgeGraph; kw...) =
  to_graphviz(to_graphviz_property_graph(g; kw...))

function to_graphviz_property_graph(g::AbstractDirectedHalfEdgeGraph;
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Union{Symbol,Bool}=false, edge_labels::Union{Symbol,Bool}=false)
  pg = PropertyGraph{Any}(; prog = prog,
    graph = graph_attrs,
    node = merge!(default_node_attrs(node_labels), node_attrs),
    edge = merge!(Dict(:arrowsize => "0.5"), edge_attrs),
  )
  for v in vertices(g)
    add_vertex!(pg, label=node_labels ? string(v) : "")
  end
  vis=Set()
  for e in half_edges(g)

    if e == inv(g,e)
      # Dangling half-edge: add an invisible vertex.
      v = add_vertex!(pg, style="invis", shape="none", label="")
      if sink(g,e)
        e′ = add_edge!(pg,v, vertex(g,e))
      else
        e′ = add_edge!(pg, vertex(g,e), v)
      end
      
      set_eprops!(pg, e′, edge_label(g, edge_labels, e))
      push!(vis, e)
    elseif e < inv(g,e)
      # Pair of distict half-edges: add a standard edge.
      if e ∉ vis
        if sink(g,e)
          e′ = add_edge!(pg, vertex(g,e), vertex(g,inv(g,e)))
        else
          e′ = add_edge!(pg, vertex(g,inv(g,e)), vertex(g,e))
        end
        set_eprops!(pg, e′, edge_label(g, edge_labels, e))
        push!(vis, e)
        push!(vis, inv(g,e))
      end
    end
  end
  pg
end

end
