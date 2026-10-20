module Chakra

# OPTION TYPE

export none, Option, obind

struct None end
none = None()
Base.show(io::IO,::None) = print(io,"none")

Option{X} = Union{X,None}

obind(::None,f::Function,v) = v
obind(::None,f::Function) = none
obind(x,f::Function,v) = f(x)
obind(x,f::Function) = f(x)

# PRODUCT TYPE

Prod{X,Y} = Pair{x,y} where {x<:X,y<:Y}

# LIST TYPE

List{X} = AbstractVector{x} where {x<:X}

export peeklast

peeklast(l::List{T}) where T = isempty(l) ? none : l[end]

export peekfirst 

peekfirst(l::List{T}) where T = isempty(l) ? none : l[1]

export droplast

droplast(l::List{T},n::Int=1) where T = @views n<length(l) ? l[1:end-n] : l[1:0]

export dropfirst

dropfirst(l::List{T},n::Int=1) where T = @views n<length(l) ? l[1+n:end] : T[]

export pos

pos(x::T,l::List{T}) where T = Base.get(findall(==(x),l),1,none)

export trimfront

trimfront(l::List{T},n::Int) where T = @views n>length(l) ? l : l[end-n+1:end]

export trimback

trimback(l::List{T},n::Int) where T = @views n>length(l) ? l : l[1:n]

export nth

nth(l::List{T},n::Int) where T = Base.get(l,n,none)

export opmap

opmap(B::Type,f::Function,l::List) = begin
    isempty(l) && return B[]
    h = f(l[1])
    h == none && return none
    t = @views opmap(B,f,l[2:end])
    t == none && return none
    return B[h,t...]
end


# ABSTRACT TYPES

abstract type Id end

abstract type Constituent end

abstract type Hierarchy end

abstract type Attribute{N,T} end

abstract type Property{N,T} end


# ATTRIBUTES

__attributes__(::Val{N}) where N = error("Attribute $N is not defined globally.")
__attributes__(N::Symbol) = __attributes__(Val{N}())
__attributes__(N::String) = __attributes__(Symbol(N))

# PROPERTIES

__properties__(::Val{N}) where N = error("Property $N is not defined globally.")
__properties__(N::Symbol) = __properties__(Val{N}())
__properties__(N::String) = __properties__(Symbol(N))


#struct Description <: Property{:description,String} end
#__properties__(::Val{:description}) = String

#struct Definition <: Property{:definition,Symbol} end
#__properties__(::Val{:definition}) = Symbol

# ABSTRACT FUNCTIONS

export geta, getp, pts, fnd, dom

function geta(::Attribute,c::Constituent) end
function getp(::Property,c::Constituent) end
function pts(c::Constituent) end
function fnd(x::Id,h::Hierarchy) end
function dom(h::Hierarchy) end

# LIST REPRESENTATION

Node = Prod{Id,Constituent}
Graph = List{Node}

# ADDITIONAL METHODS FOR THE ABSTRACT FUNCTIONS

geta(n::Union{Symbol,String},c::Constituent) = geta(__attributes__(n),c)
geta(a::Union{Attribute,Symbol,String},x::Id,h::Union{Hierarchy,Module,Graph}) = obind(fnd(x,h),c->geta(a,c))

getp(n::Union{Symbol,String},c::Constituent) = getp(__properties__(n),c)
getp(p::Union{Property,Symbol,String},x::Id,h::Union{Hierarchy,Module,Graph}) = obind(fnd(x,h),c->getp(p,c))

pts(x::Id,h::Union{Hierarchy,Module,Graph}) = obind(fnd(x,h),pts)

fnd(x::Id,m::Module) = fnd(x,m.__data__)
fnd(x::Id,h::Graph) = obind(pos(x,dom(h)),n->last(h[n]))
fnd(xs::List{Id},h::Union{Hierarchy,Module,Graph}) = Option{Constituent}[fnd(x,h) for x in xs]

dom(h::Module) = dom(h.__data__)
dom(h::Graph) = first.(h)

# ADDITIONAL FUNCTIONS

export fnd!

fnd!(x::Id,h::Union{Hierarchy,Module,Graph}) = obind(fnd(x,h),c->c,error("$x not found."))
fnd!(xs::List{Id},h::Union{Hierarchy,Module,Graph}) = Constituent[fnd(x,h) for x in xs if mem(x,h)]

export sequence

sequence(xs::List{Id},h::Union{Hierarchy,Module,Graph}) = fnd(xs,h)

export sequence!

sequence!(xs::List{Id},h::Union{Hierarchy,Module,Graph}) = fnd!(xs,h)

# LENGTH OF A HIERARCHY
Base.length(h::Union{Hierarchy,Module}) = length(dom(h))

# TEST IF HIERARCHY IS EMPTY
Base.isempty(h::Union{Hierarchy,Module}) = isempty(dom(h))

export pos

pos(x::Id,h::Union{Hierarchy,Module,Graph}) = pos(x,dom(h))

export startingat

startingat(n::Int,h::Graph) = @views h[n:end]
startingat(x::Id,h::Graph) = obind(pos(x,h),n->startingat(n,h),Node[])
startingat(x::Union{Int,Id},h::Union{Hierarchy,Module}) = startingat(x,cts(h))

export endingat

endingat(n::Int,h::Graph) = @views h[1:n]
endingat(x::Id,h::Graph) = obind(pos(x,h),n->endingat(n,h),Node[])
endingat(x::Union{Int,Id},h::Union{Hierarchy,Module}) = endingat(x,cts(h))

export level

level(x::Id,h::Union{Hierarchy,Module,Graph}) = begin
    !mem(x,h) && return none
    ps = pts(x,h)
    isempty(ps) && return 1
    plevs = unique([level(p,h) for p in ps])
    length(plevs) != 1 && return none
    return plevs[1]+1
end

export isdatasource

isdatasource(m::Module) = isdefined(m,:__data__) && m.__data__ isa Hierarchy

export cts

cts(h::Union{Hierarchy,Module}) = Pair{Id,Constituent}[Pair(x,fnd(x,h)) for x in dom(h)]
cts(h::Graph) = h::Vector{Pair{Id,Constituent}}

export mem

mem(x::Id,d::List{Id}) = x in d
mem(x::Id,h::Union{Hierarchy,Module,Graph}) = mem(x,dom(h))
mem(xs::List{Id},h::Union{Hierarchy,Module,Graph}) = all([mem(x,h) for x in xs])

export subparts

subparts(x::Id,h::Graph) = begin
    isempty(h) && return Id[]
    c = fnd(x,h)
    c == none && return Id[]
    res = Id[x]
    ps = pts(c)
    [union!(res,subparts(p,endingat(p,h))) for p in ps]
    return sort!(res, by = x -> pos(x,h))
end

subparts(xs::List{Id},h::Graph) = begin
    res = Id[]
    [union!(res,subparts(x,h)) for x in xs]
    return sort!(res, by = x -> pos(x,h))
end

subparts(x::Union{Id,List{Id}},h::Union{Hierarchy,Module}) = subparts(x,cts(h))

export superparts

superparts(x::Id,h::Graph) = begin
    res = Id[]
    h2 = startingat(x,h)
    for y in dom(h2)
        if x in pts(y,h2)
            push!(res,y)
            union!(res,superparts(y,h2))
        end
    end
    return sort!(res, by = x->pos(x,h))
end

superparts(xs::List{Id},h::Graph) = begin
    res = Id[]
    [union!(res,superparts(x,h)) for x in xs]
    return sort!(res, by = x->pos(x,h))
end

superparts(x::Union{Id,List{Id}},h::Union{Hierarchy,Module}) = superparts(x,cts(h))

export aggregates

aggregates(x::Id,h) = begin 
    Id[y for y in dom(h) if haspart(y,x,h)]
end

export top

top(h::Union{Hierarchy,Module,Graph}) = Id[x for x in dom(h) if aggregates(x,h) == []]

export bottom

bottom(h::Union{Hierarchy,Module,Graph}) = Id[x for x in dom(h) if pts(x,h) == []]

export siblings

siblings(x::Id,y::Id,h::Union{Hierarchy,Module}) = begin
    !haspart(y,x,h) && return none
    return filter(!=(x),pts(y,h))
end

export lsiblings

lsiblings(x::Id,y::Id,h::Union{Hierarchy,Module}) = begin
    ps = pts(y,h)
    return obind(pos(x,ps),p->ps[1:p-1],none)
end

export rsiblings

rsiblings(x::Id,y::Id,h::Union{Hierarchy,Module}) = begin
    ps = pts(y,h)
    return obind(pos(x,ps),p->ps[p+1:end],none)
end

export hasa

hasa(a::Union{Property,Symbol,String},c::Constituent,v) = geta(a,c) == v
hasa(a::Union{Property,Symbol,String},x::Id,v,h::Union{Hierarchy,Module,Graph}) = geta(a,x,h) == v
hasa(a::Union{Property,Symbol,String},x::Id,h::Union{Hierarchy,Module,Graph}) = geta(a,x,h) != none

export hasp

hasp(p::Union{Property,Symbol,String},c::Constituent,v) = getp(p,c) == v
hasp(p::Union{Property,Symbol,String},x::Id,v,h::Union{Hierarchy,Module,Graph}) = getp(p,x,h) == v
hasp(p::Union{Property,Symbol,String},x::Id,h::Union{Hierarchy,Module,Graph}) = getp(p,x,h) != none

export haspart

haspart(x::Id,y::Id,h::Union{Hierarchy,Module,Graph}) = y in pts(x,h)

export ispartof

ispartof(x::Id,y::Id,h::Union{Hierarchy,Module,Graph}) = haspart(y,x,h)

export hassubpart

hassubpart(x,y,h) = y in subparts(x,h)

export issubpartof

issubpartof(x,y,h) = hassubpart(y,x,h)

export incomparable

incomparable(x::Id,y::Id,h::Union{Hierarchy,Module,Graph}) = !(hassubpart(x,y,h) || hassubpart(y,x,h))
incomparable(ps::List{Id},h::Union{Hierarchy,Module,Graph}) = all([incomparable(ps[i],ps[j],h) for i in 1:length(ps)-1 for j in i+1:length(ps)])

export disjoint

disjoint(l1::Vector,l2::Vector) = intersect(l1,l2) == []
disjoint(ls::Vector{Vector}) = all([disjoint(ls[i],ls[j]) for i in 1:length(ls)-1 for j in i+1:length(ls)])
disjoint(x::Id,y::Id,h::Union{Hierarchy,Module,Graph}) = disjoint(subparts(x,h),subparts(y,h))
disjoint(xs::List{Id},h::Union{Hierarchy,Module,Graph}) = all([disjoint(xs[i],xs[j],h) for i in 1:length(xs)-1 for j in i+1:length(xs)])

export hassibling

hassibling(x,y,z,h) = y in siblings(x,z,h)

export haslsibling

haslsibling(x,y,z,h) = y in lsiblings(x,z,h)

export hasrsibling

hasrsibling(x,y,z,h) = y in rsiblings(x,z,h)

export issiblingof

issiblingof(x,y,z,h) = x in siblings(y,z,h)

export islsiblingof

islsiblingof(x,y,z,h) = x in lsiblings(y,z,h)

export isrsiblingof

isrsiblingof(x,y,z,h) = x in rsiblings(y,z,h)

export wf

wf(x::Id,ps::List{Id},d::List{Id}) = !mem(x,d) && mem(ps,d)
wf(x::Id,c::Constituent,d::List{Id}) = wf(x,pts(c),d)
wf(c::Node,d::List{Id}) = wf(c[1],c[2],d)
wf(c::Node,h::Union{Hierarchy,Module,Graph}) = wf(c,dom(h))

export isdag

isdag(h::Graph) = all([wf(h[i],endingat(i-1,h)) for i in 1:length(h)])
isdag(h::Union{Hierarchy,Module}) = isdag(cts(h))

export balanced

balanced(x::Id,h::Union{Hierarchy,Module,Graph}) = obind(pts(x,h),ps->incomparable(ps,h),false)
balanced(h::Union{Hierarchy,Module,Graph}) = all([balanced(x,h) for x in dom(h)])

export istree

istree(x::Id,h::Union{Hierarchy,Module,Graph}) = begin
    isempty(h) && return false
    !mem(x,h) && return false
    ps = pts(x,h)
    isempty(ps) && return true
    return all([istree(p,endingat(p,h)) for p in ps]) && disjoint(ps,h) 
end
istree(h::Union{Hierarchy,Module,Graph}) = (r = top(h); length(r) == 1 && istree(r[1],h))

export ismultitree

ismultitree(xs::List{Id},h::Union{Hierarchy,Module,Graph}) = mem(xs,h) && all([istree(x,h) for x in xs])
ismultitree(h::Union{Hierarchy,Module,Graph}) = ismultitree(top(h),h)

export stratisfied

stratisfied(h::Union{Hierarchy,Module,Graph}) = all([level(x,h)!=none for x in top(h)])
stratisfied(p::Union{Property,Symbol,String},vs::Vector,h::Union{Hierarchy,Module,Graph}) = all([obind(level(x,h),l->length(vs)<l ? false : hasp(p,x,vs[l],h),false) for x in dom(h)])



# VIEWPOINTS

abstract type Viewpoint{T} end

returntype(v::Viewpoint{T}) where T = T

struct AtomicViewpoint{T} <: Viewpoint{T}
    attribute::Attribute
    returntypes::List{Type}
    AtomicViewpoint(a::Attribute{N,T}) where {N,T} = new{T}(a,[T])
    AtomicViewpoint(a::Symbol) = AtomicViewpoint(__attributes__(a))
    AtomicViewpoint(a::String) = AtomicViewpoint(__attributes__(a))
end

function (v::AtomicViewpoint{T})(s::List)::Option{T} where T 
    obind(lpeek(s), o->geta(v.attribute,o))
end

struct LinkedViewpoint{T} <: Viewpoint{T}
    components::List{Viewpoint}
    returntypes::List{DataType}
    LinkedViewpoint(v1::Viewpoint,v2::Viewpoint,vs::Viewpoint...) = begin
        components = [v1,v2,vs...]
        returntypes = [returntype(c) for c in components]
        new{Tuple{returntypes...}}(components,returntypes)
    end
end

function (v::LinkedViewpoint{T})(s::List)::Option{T} where T
    res = []
    for c in v.components
        val = c(s)
        if val == none
            return none
        end
        push!(res,val)
    end
    #print(res)
    return Tuple(res)
end

struct DerivedViewpoint{T} <: Viewpoint{T}
    base::Viewpoint
    modifier::Function
    returntypes::Vector{DataType}
    DerivedViewpoint(v::Viewpoint,f::Function) = begin
        t = Base._return_type(f,Tuple{v.returntypes...})
        if t == Union{}
            error("Type mismatch: The function $f is not composable with the viewpoint $v")
        end
        new{t}(v,f,[t])
    end
end

function (v::DerivedViewpoint{T})(s::Vector)::Option{T} where T
    n = length(v.base.returntypes)
    if n == 1
        obind(v.base(s),(x)->v.modifier(x))
    end
    obind(v.base(s),(x)->v.modifier(x...))
end

struct DelayedViewpoint{T} <: Viewpoint{T}
    base::Viewpoint{T}
    lag::Int64
end

function (v::DelayedViewpoint{T})(s::Vector)::Option{T} where T 
    v.base(lpopn(s,v.lag))
end

struct ThreadedViewpoint{T} <: Viewpoint{T}
    base::Viewpoint{T}
    test::Viewpoint{Bool}
end

function (v::ThreadedViewpoint{T})(s::Vector)::Option{T} where T
    v.test(s) ? v.base(s) : none
end


# Viewpoint constructor interface

vp(x::Attribute) = AtomicViewpoint(x)

link(v1::Viewpoint,v2::Viewpoint,vs::Viewpoint...) = LinkedViewpoint(v1,v2,vs...)

compose(v::Viewpoint,f::Function) = DerivedViewpoint(v,f)

delay(v::Viewpoint,l::Int) = DelayedViewpoint(v,l)

thread(b::Viewpoint,t::Viewpoint) = ThreadedViewpoint(b,t)

# Additional viewpoint constructors

diff(v::Viewpoint{T}) where T = compose(link(v,delay(v,1)),(x,y)->x-y)

include("diff-generic.jl")

# isdiffable(v::Viewpoint{T}) where T = TODO : how to check whether T has a "-"


function vp_map(v::Viewpoint{T},s::Vector)::List{Option{T}} where T

    # Maps a viewpoint of a sequence

    return [v(s[1:n]) for n in 1:length(s)]
end



end # module
