module DirectedHalfEdgeGraphs

using Reexport


export SchDirectedHalfEdgeGraph, AbstractDirectedHalfEdgeGraph, DirectedHalfEdgeGraph, sink, source, in_edges, out_edges, half_edge_pairs,  dangling_edges, cycle_basis,subtree,nickel_index,sort,to_cat_format,nh,_add_half_edges!,paired_half_edges,edge_index,add_half_edges!,kruskal,nloops

using Catlab.Graphs
@reexport import Catlab.Graphs.BasicGraphs: inv,add_half_edge_pairs!, add_half_edge_pair!, nv, src, tgt, edges,neighbors, inneighbors, outneighbors, all_neighbors, degree, half_edges, add_dangling_edge!, add_dangling_edges!,ne
@reexport import Catlab.Graphs.Searching: dfs_parents, tree
@reexport import Catlab.Graphics.GraphvizGraphs: to_graphviz, to_graphviz_property_graph

using Catlab
using MLStyle
using DataStructures: IntDisjointSets
using DataStructures
import StatsBase:countmap
using Base: @invoke
using Catlab.CategoricalAlgebra, Catlab.Graphics, Catlab.Graphs, Catlab.Graphics.GraphvizGraphs
import Catlab.Theories: src, tgt

@present SchDirectedHalfEdgeGraph <: SchHalfEdgeGraph begin
  Truth::AttrType
  sink::Attr(H, Truth)
end

@abstract_acset_type AbstractDirectedHalfEdgeGraph <: AbstractHalfEdgeGraph


@acset_type DirectedHalfEdgeGraphGeneric(SchDirectedHalfEdgeGraph, index=[:inv, :vertex, :sink]) <: AbstractDirectedHalfEdgeGraph

DirectedHalfEdgeGraph = DirectedHalfEdgeGraphGeneric{Bool}


#******************************************************************************
# Accessors 

"""
    sink(DirectedHalfEdgeGraph,edge(s))
  
Gives the sink of an edge(s), as a vector of bools.
"""
sink(g::AbstractDirectedHalfEdgeGraph, args...;kws...) = subpart(g, args..., :sink)


"""
  source(DirectedHalfEdgeGraph,edge(s))

Gives the source of an edge(s), as a vector of bools.
"""
source(g::AbstractDirectedHalfEdgeGraph, args...) = .!subpart(g, args..., :sink)

function fixinv!(g::AbstractDirectedHalfEdgeGraph) 
  for h in half_edges(g)
    inv(g,h) ==0 && set_subpart!(g, h, :inv, h)
  end
  g
end




half_edges(g::AbstractDirectedHalfEdgeGraph;by::Function=identity,kws...) = Base.sort(parts(g, :H); by=by,kws...)
half_edges(g::AbstractDirectedHalfEdgeGraph, v;by::Function=identity,kws...) = Base.sort(incident(g, v, :vertex);by=by,kws...)


""" 
    in_edges(graph)

Vector of incoming half edges
"""
in_edges(g::AbstractDirectedHalfEdgeGraph,args...;kws...) = filter(h->sink(g,h),half_edges(g,args...;kws...))



"""
    out_edges(graph)

Vector of outgoing half-edges in graph.
"""
out_edges(g::AbstractDirectedHalfEdgeGraph,args...;kws...) = filter(h->source(g,h),half_edges(g,args...;kws...))




function paired(g::AbstractDirectedHalfEdgeGraph, H)
  notSelf = H .!= inv(g, H)
  return H[notSelf]
end

function dangling(g::AbstractDirectedHalfEdgeGraph, H)
  self = H .== inv(g, H)
  return H[self]
end

function paired_half_edges(g::AbstractDirectedHalfEdgeGraph, v;kws...)
  paired(g, half_edges(g, v;kws...))
end

function paired_half_edges(g::AbstractDirectedHalfEdgeGraph;kws...)
  paired(g, half_edges(g;kws...))

end


"""
    edges(graph)

    Returns the edges in a half-edge graph. The edges are returned as a pair of
    vectors of vertices. We don't count dangling edges.
"""
function edges(g::AbstractDirectedHalfEdgeGraph;kws...)
  pH = paired_half_edges(g;kws...)
  tgts = pH[sink(g, pH)]
  srcs = inv(g, tgts)
  return (vertex(g, srcs), vertex(g, tgts))
end

function edges(g::AbstractDirectedHalfEdgeGraph, src::Int, tgt::Int;kws...)
  H = half_edge_pairs(g, src, tgt;kws...)
  return (vertex(g, H[1]), vertex(g, H[2]))
end



""" 
    src(graph,edge[edges])

Source vertex (vertices) of edges(s) in a graph.
"""
function src(g::AbstractDirectedHalfEdgeGraph;kws...)
  pH = paired_half_edges(g;kws...)
  srcs = pH[source(g, pH)]
  return vertex(g, srcs)
end

function src(g::AbstractDirectedHalfEdgeGraph, e;kws...)
  return src(g;kws...)[e]
end

""" 
    tgt(graph,edge[edges])

Target vertex (vertices) of edges(s) in a graph.
"""
function tgt(g::AbstractDirectedHalfEdgeGraph;kws...)
  pH = paired_half_edges(g;kws...)
  tgts = pH[sink(g, pH)]
  return vertex(g, tgts)
end

function tgt(g::AbstractDirectedHalfEdgeGraph, e;kws...)
  return tgt(g;kws...)[e]
end




"""
    nh(graph)

    Returns the number of half-edges in a half-edge graph.
"""
function nh(g::AbstractDirectedHalfEdgeGraph)
  return nparts(g, :H)
end

function nh(g::AbstractDirectedHalfEdgeGraph, v)
  return length(half_edges(g, v))
end

function ne(g::AbstractDirectedHalfEdgeGraph)
  return length(paired_half_edges(g))/2
end

function ne(g::AbstractDirectedHalfEdgeGraph, v)
  return length(paired_half_edges(g, v))/2
end

function half_edge_pairs(g::AbstractDirectedHalfEdgeGraph, src::Int, tgt::Int; dir=false,kws...)
  out = dir ? out_edges(g, src;kws...) : half_edges(g, src;kws...)
  in = inv(g, out)
  has_tgt = vertex(g, in) .== tgt
  return (out[has_tgt], in[has_tgt])
end

function half_edge_pairs(g::AbstractDirectedHalfEdgeGraph;kws...)
  out = out_edges(g;kws...)
  in = inv(g, out)
  is_inner = in .!= out
  (out[is_inner], in[is_inner])
end


""" Neighbors of vertex in a graph.
In a graph, this function is an alias for [`outneighbors`](@ref); in a symmetric
graph, a vertex has the same out-neighbors and as in-neighbors, so the
distinction is moot.
In the presence of multiple edges, neighboring vertices are given *with
multiplicity*. To get the unique neighbors, call `unique(neighbors(g))`.
"""
@inline neighbors(g::AbstractDirectedHalfEdgeGraph, v::Int) = outneighbors(g, v)
function _neighbors(g::AbstractDirectedHalfEdgeGraph, v::Int,neighborFct::Function;kws...)
  vertex(g,inv(g,paired(g,neighborFct(g, v;kws...))))
end


""" In-neighbors of vertex in a graph.
"""
inneighbors(g::AbstractDirectedHalfEdgeGraph, v;kws...) = _neighbors(g,v,in_edges;kws...)

""" Out-neighbors of vertex in a graph.
    Returns the vertices that are neighbors of the given vertex.
"""
outneighbors(g::AbstractDirectedHalfEdgeGraph, v;kws...) = _neighbors(g,v,out_edges;kws...)




""" Union of in-neighbors and out-neighbors in a graph.
"""
all_neighbors(g::AbstractDirectedHalfEdgeGraph, v::Int;kws...) = _neighbors(g,v,half_edges;kws...)


""" Total degree of a vertex
Equivalent to length(all_neighbors(g,v)) but faster
"""
degree(g, v) = nh(g, v)

function dangling_edges(g::AbstractDirectedHalfEdgeGraph, vertices...; dir=:both,kws...)
  H = @match dir begin
    :both => half_edges(g, vertices...;kws...)
    :in => in_edges(g, vertices...;kws...)
    :out => out_edges(g, vertices...;kws...)
  end
  is_dangling = inv(g, H) .== H
  return H[is_dangling]
end


"""
    nickel_index(graph)



    http://users.physik.fu-berlin.de/~kleinert/nickel/guelph.pdf
"""
function nickel_index(g::AbstractHalfEdgeGraph)
  edge_index(g)
end

function edge_index(g::AbstractHalfEdgeGraph)
  
  index=""
  for v ∈ vertices(g)
  
    nout=length(dangling_edges(g, v; dir=:out))
    index*=string("|",repeat("o ",nout))
    nin=length(dangling_edges(g, v; dir=:in))
    index*=string(repeat("i ",nin))  
    ns=Base.sort(all_neighbors(g,v))
    newns=ns[ns.>v]
    index*=string(join(string.(newns)," "))
  
  end
  index *= "|"

  index
end
#******************************************************************************
#Constructors

function (::Type{T})(inv::AbstractVector{Int},vertex::AbstractVector{Int},sink::AbstractVector{Bool}=zeros(Bool,length(inv)),args...;kw...) where T <: AbstractDirectedHalfEdgeGraph
  g = T()
  add_half_edges!(g,inv,vertex,sink,args...;kw...)
  return g
end



function (::Type{T})(H::AbstractVector{Int},H′::AbstractVector{Int},vs::AbstractVector{Int},args...;kw...) where T <: AbstractDirectedHalfEdgeGraph
  
  Ins=to_cat_format!(H,H′)
  nh=length(H)
  inv =FinFunction(Dict(H.=>H′ )).(1:nh)
  vertex=FinFunction(Dict(H.=>vs )).(1:nh)
  sink=FinFunction(Dict(H.=>Ins )).(1:nh)

  T(inv,vertex,sink,map(x->FinFunction(Dict(H.=>x )).(1:nh),args)...;kw...)
end

function to_cat_format!(H::AbstractVector{Int},H′::AbstractVector{Int})
  nh = length(H)
  Ins=map(x->x<0&&iseven(-x),H).||(H.>H′)
  isExt=(H′.==0)
  H.+=(isExt).*(nh+1)
  H′[isExt]=H[isExt]
  Ins
end



#******************************************************************************
# Muttators

function _add_half_edges!(g::AbstractDirectedHalfEdgeGraph, inv::AbstractVector{Int},vertex::AbstractVector{Int},sink::AbstractVector{Bool}=zeros(Bool,length(inv));strict=false,kw...)
  @assert all(inv.>0)
  @assert all(vertex.>0)

  for (src,tgt) in Iterators.filter(((x,y),)->x!=y,enumerate(inv))
    if strict
      @assert sink[src]!=sink[tgt] "$src and $tgt are either both sources or both sinks"
    else
      sink[tgt]=(!sink[src])
    end
  end
  nnewv=maximum(vertex)-nv(g)

  add_parts!(g,:V,nnewv) 
  add_parts!(g, :H, length(inv); vertex=vertex,inv=nh(g) .+inv,sink=sink, kw...)
end

function add_half_edges!(g::AbstractDirectedHalfEdgeGraph, inv::AbstractVector{Int},vertex::AbstractVector{Int},sink::AbstractVector{Bool}=zeros(Bool,length(inv));strict=false,kw...)

  _add_half_edges!(g, inv, vertex, sink; strict, kw...)

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
  H = add_part!(g, :H; vertex=v, inv=nparts(g, :H) + 1, sink=dir, kw...)
end

function add_dangling_edges!(g::AbstractDirectedHalfEdgeGraph, vs::AbstractVector{Int}; dirs::AbstractVector{Bool}, kw...)
  n, k = length(vs), nparts(g, :H)
  H = add_parts!(g, :H, n; vertex=vs, inv=(k+1):(k+n), sink=dirs, kw...)
end

#******************************************************************************
# Searching


Base.sort(g::AbstractDirectedHalfEdgeGraph, edges) = edges

"""
The algorithm may be concisely expressed as follows.
Let E be the set of edges and V the set of vertices of the
given graph. Let T be the set of vertices already in the
spanning tree, and let X be the set of vertices not yet
"examined" as defined below. Initially T = ∅, X = V.
Take any vertex v from X as the root of the tree. Then
T = {v}, X = V.
Let z be any vertex in T ∩ X. If there are none, the proc-
ess is complete. Now examine the vertex z ; i.e. consider
each edge z - w in E and act as follows. If w ∈ T you have found the
fundamental cycle consisting of z - w together with the
unique path in the tree from w to z. If w ∉ T add edge
z - w to the tree and therefore w to T. In each case delete
edge w - z from E. When all edges z - w have been con-
sidered, remove this current z from X and repeat the
process with a new z.
"""
function cycle_basis(g₀::AbstractDirectedHalfEdgeGraph, root=nothing)
  g = copy(g₀)

  not_examined = unique!(Vector{Int}(vertices(g)))
  cycles = Vector{Vector{Int}}()

  nv(g) == 0 && return cycles
  r = (root == nothing) ? first(not_examined) : root
  cycle_tree = zeros(Int,nv(g))
  cycle_tree[r] = r
  T=Int[r]
  Trunk=Int[]

  while !isdisjoint(T, not_examined)
    z = T[findlast(x -> x ∈ not_examined, T)]

    @info "add $z to trunk"
    push!(Trunk,z)

    while !isempty(paired_half_edges(g, z))
      w = vertex(g, inv(g, first(paired_half_edges(g, z))))
      @info "look at $w from  $z"
      rem_edge!(g, z, w)
      if w ∈ T
        @info "$w - $z closes cycle"
        push!(cycles, cycle(cycle_tree,(w,z),Trunk))
      else
        @info "add $w to cycle tree"  
        push!(T, w)
        cycle_tree[w] = z
      end
    end
    setdiff!(not_examined, [z])
  end

  return cycles
end



function cycle(parenttree::AbstractVector{Int},(v,w)::Tuple{Int,Int},trunk::AbstractVector{Int})
  pv=parenttree[v]
  pw=parenttree[w]
  ipv=findfirst(isequal(pv),trunk)
  ipw=findfirst(isequal(pw),trunk)
  if v == w
    return [v]
  elseif v == pw
    return [v,w]
  elseif w == pv
    return [w,v]
elseif pv==pw
    return [v,w,pw]
  else 
    if ipv<ipw
      return [v,(trunk[ipv:ipw])...,w]
    else
      return [v,(trunk[ipw:ipv])...,w]
    end
  end
end


function dfs_parents(g::AbstractDirectedHalfEdgeGraph, s::Int, neighborfn::Function; kws...)
  
  parents = zeros(Int, nv(g))
  seen = zeros(Bool, nv(g))
  S = [s]
  seen[s] = true
  parents[s] = s
  while !isempty(S)
    v = S[end]
    u = 0
    for n in neighborfn(g, v;kws...)
      

      if !seen[n]
        u = n
        break
      end
    end
    if u == 0
      pop!(S)
    else
      seen[u] = true
      push!(S, u)
      parents[u] = v
    end
  end
  return parents
end


function tree(parents::AbstractVector{Int})
  n=length(parents[parents .> 0])
  t = Graph(n)
  for (v, u) in enumerate(parents)
    if u > 0 && u != v
      add_edge!(t, u, v)
    end
  end
  return t
end

function subtree(g::AbstractDirectedHalfEdgeGraph,parents::AbstractVector{Int})
  n=length(parents)
  H=Vector{Int}()
  V=(1:n)[parents.>0]
  for (v, u) in enumerate(parents)
    if u > 0 && u != v
      append!(H, first(zip(half_edge_pairs(g,u, v)...)))
    end
  end
  return Subobject(g, H=H, V=V)
end

function nloops(g::AbstractDirectedHalfEdgeGraph)
  return length(cycle_basis(g))
end



function kruskal(g::AbstractDirectedHalfEdgeGraph,weightfun::Function;kws...)
  nconn=length(connected_components(g))
  connected_vs = IntDisjointSets(nv(g))
  F=Subobject(g,V=vertices(g))
  for (u,v) in zip(half_edge_pairs(g;by=h->weightfun(g,h),kws...)...)
    @info "looking at half edges $u - $v from $(vertex(g,u)) to $(vertex(g,v)), with weight $(weightfun(g,u))"
    if !in_same_set(connected_vs, vertex(g,u), vertex(g,v))
      @info "adding edge $(vertex(g,u)) - $(vertex(g,v))"
      edge=Subobject(g,H=[u,v],V=[vertex(g,u),vertex(g,v)])
      F=F ∨ edge
      union!(connected_vs, vertex(g,u), vertex(g,v))
    end
  end
  return F
end


#******************************************************************************
# Displaying  


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
    pg = PropertyGraph{Any}(; prog=prog,
      graph=graph_attrs,
      node=merge!(default_node_attrs(node_labels), node_attrs),
      edge=merge!(Dict(:arrowsize => "0.5"), edge_attrs)
    )
    for v in vertices(g)
      add_vertex!(pg, label=node_labels ? string(v) : "")
    end
    for h in dangling_edges(g)
      # Dangling half-edge: add an invisible vertex.
      v = add_vertex!(pg, style="invis", shape="none", label="")
      if sink(g, h)
        e′ = add_edge!(pg, v, vertex(g, h))
      else
        e′ = add_edge!(pg, vertex(g, h), v)
      end
      set_eprops!(pg, e′, edge_label(g, edge_labels, h))
    end
    for (src,tgt) ∈ zip(edges(g)...)
      e = add_edge!(pg, src,tgt)
      set_eprops!(pg, e, edge_label(g, edge_labels, e))
    end
    pg
  end



to_graphviz(subgraph::Subobject{<:AbstractDirectedHalfEdgeGraph}; kw...) =
  to_graphviz(to_graphviz_property_graph(subgraph; kw...))

function to_graphviz_property_graph(
    subgraph::Subobject{<:AbstractDirectedHalfEdgeGraph};
    subgraph_node_attrs::AbstractDict=Dict(:color => "cornflowerblue"),
    subgraph_edge_attrs::AbstractDict=Dict(:color => "cornflowerblue"), kw...)
  pg = to_graphviz_property_graph(ob(subgraph); kw...)
  f = hom(subgraph)
  fixinv!(dom(f))
  for v in vertices(dom(f))
    set_vprops!(pg, f[:V](v), subgraph_node_attrs)
  end
  for ((src,tgt),mult) in countmap(zip(edges(dom(f))...))
    Es=collect(edges(pg.graph,f[:V](src),f[:V](tgt)))[1:mult]
    for e in Es
      set_eprops!(pg, e, subgraph_edge_attrs)
    end
  end
  pg
end

end
