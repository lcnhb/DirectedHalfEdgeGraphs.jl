function to_cat_format(H::AbstractVector{Int},H′::AbstractVector{Int})
  nh = length(H)
  Ins=map(x->x<0&&iseven(-x),H)
  isExt=(H′.==0)
  H.+=(isExt).*(nh+1)
  H′[isExt]=H[isExt]
  (H,H′,Ins)
end

H           = [-2,1,3,-1,-4,2,4,-3]
Hdual       = [0,2,4,0,0,1,3,0]
vertex      = [1,1,1,1,2,2,2,2]


to_cat_format(H, Hdual)
H
Hdual
to_cat_format(H, Hdual)
FinFunction(Dict(H.=>H′ )).(1:nh)