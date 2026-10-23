"""

# Chakra Version 2.0

"""
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

# LIST REPRESENTATION OF HIERARCHIES

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
mem(xs::List{Id},d::List{Id}) = all([mem(x,d) for x in xs])
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


# OPERATIONS ON HIERARCHIES

abstract type READ{A} end

abstract type CMD{A,B} end

struct APP{B} <: READ{B}
    name
    op
    args
    APP(F::CMD{A,B},a::A) where {A,B} = new{B}("APP",F.op(a),[F,a])
end

(R::READ{A})(h::Union{Hierarchy,Module,Graph}) where A = R.op(h)::Option{A}

(K::CMD{A,B})(a::A) where {A,B} = APP(K,a)
(K::CMD{A,B})(a::A,h::Union{Hierarchy,Module,Graph}) where {A,B} = K(a)(h)


export RET

struct RET{A} <: READ{A}
    name
    op
    args
    RET(v::A) where A = new{A}("RET",_->v,[v])
end

export BIND

struct BIND{A,B} <: READ{B}
    name
    op
    args
    BIND(R::READ{A},F::CMD{A,B}) where {A,B} = new{A,B}("BIND",h->F(R(h),h),[R,F])
end

export FISH

struct FISH{A,B} <: CMD{A,B}
    name
    op
    args
    FISH(F::CMD{A,B1},G::CMD{B2,C}) where {A,B2,B1<:B2,C} = new{A,C}("FISH",x->h->G(F(x,h),h),[F,G])
end

BIND(R::READ,KS::CMD...) = BIND(R,FISH(KS...))
FISH(f::CMD,g::CMD...) = isempty(g) ? f : FISH(f,FISH(g...))

export MAP

struct MAP{A,B} <: CMD{List{A},List{B}}
    name
    op
    args
    MAP(F::CMD{A,B}) where {A,B} = new{A,B}("MAP",l->h->opmap(B,x->F(x,h),l),[F])
end

export DOM

struct DOM <: READ{List{Id}}
    name
    op
    args
    DOM() = new("DOM",h->dom(h),[])
end

export GETA

struct GETA{N,T} <: CMD{Id,T}
    name
    op
    args
    GETA(A::Attribute{N,T}) where {N,T} = new{N,T}("GETA",x->h->geta(A,x,h),[A])
    GETA(N::Union{Symbol,String}) = GETA(__attributes__(N))
end

export GETP

struct GETP{N,T} <: CMD{Id,T}
    name
    op
    args
    GETP(P::Property{N,T}) where {N,T} = new{N,T}("GETP",x->h->getp(P,x,h),[P])
    GETP(N::Union{Symbol,String}) = GETP(__properties__(N))
end

export PTS

struct PTS <: CMD{Id,List{Id}}
    name
    op
    args
    PTS() = new("PTS",x->h->pts(x,h),[])
end

export SUBCS

struct SUBCS <: CMD{Id,List{Id}}
    name
    op
    args
    SUBCS() = new("SUBCS",c->cs->subparts(c,cs),[])
end


# PREDICATES

abstract type PROP <: READ{Bool} end
abstract type PRED{T} <: CMD{T,Bool} end
abstract type REL{A,B} <: CMD{Prod{A,B},Bool} end

# TODO isdag etc
# TODO lift 

abstract type CPROP <: PRED{Id} end
abstract type CREL <: REL{Id,Id} end
abstract type LPROP <: PRED{List{Id}} end
abstract type LREL <: REL{List{Id},List{Id}} end

export HASA

struct HASA{N,T} <: CPROP
    name
    op
    args
    HASA(a::Attribute{N,T},v::t) where {N,T,t<:T} = new{N,T}("HASA",x->h->geta(a,x,h)==v,[a,v])
    HASA(a::Attribute{N,T}) where {N,T} = new{N,T}("HASA",x->h->geta(a,x,h)!= none,[a])
    HASA(N::Union{Symbol,String},v) = HASA(__attributes__(N),v)
    HASA(N::Union{Symbol,String}) = HASA(__attributes__(N))
end

export HASP

struct HASP{N,T} <: CPROP
    name
    op
    args
    HASP(p::Property{N,T},v::t) where {N,T,t<:T} = new{N,T}("HASP",x->h->getp(p,x,h)==v,[p,v])
    HASP(p::Property{N,T}) where {N,T} = new{N,T}("HASP",x->h->getp(p,x,h)!=none,[p])
    HASP(N::Union{Symbol,String},v) = HASP(__properties__(N),v)
    HASP(N::Union{Symbol,String}) = HASP(__properties__(N))
end

export PARTS

struct PARTS <: CPROP
    name
    op
    args
    PARTS(P::LPROP) = new("PARTS",x->h->obind(pts(x,h),ps->P(ps,h)),[P])
end

export ALL

struct ALL <: LPROP
    name
    op
    args
    ALL(P::CPROP) = new("ALL",xs->h->all([P(x,h) for x in xs]),[P])
end

export SOME

struct SOME <: LPROP
    name
    op
    args
    SOME(P::CPROP) = new("SOME",xs->h->any([P(x,h) for x in xs]),[P])
end

export NTH

struct NTH <: LPROP
    name 
    op
    args
    NTH(n::Int,P::CPROP) = new("NTH",xs->h->P(xs[n],h),[n,P])
end 

export FIRST

struct FIRST <: LPROP
    name
    op
    args
    FIRST(T::CPROP) = new("FIRST",xs->h->(isempty(ps) ? false : T(first(xs),h)),[T])
    FIRST(x::Id) = new("FIRST",xs->h->(isempty(xs) ? false : first(xs)==x),[x])
end

export LAST

struct LAST <: LPROP
    name
    op
    args
    LAST(T::CPROP) = new("LAST",xs->h->(isempty(ps) ? false : T(last(xs),h)),[T])
    LAST(x::Id) = new("LAST",xs->h->(isempty(xs) ? false : last(xs)==x),[x])
end

export NIL

struct NIL <: LPROP
    name
    op
    args
    NIL() = new("NIL",xs->h->isempty(xs),[])
end

export CONS

struct CONS <: LPROP
    name 
    op 
    args
    CONS(C::CPROP,L::LPROP) = new("CONS",xs->h->C(xs[1],h)&& L(xs[2:end],h),[C,L])
end
CONS(C::CPROP,CS::CPROP...) = isempty(CS) ? CONS(C,NIL()) : CONS(C,CONS(CS...))

export PAIRWISE

struct PAIRWISE <: LREL
    name
    op
    args
    PAIRWISE(R::CREL) = begin 
        function pw(P,h)
            l1,l2 = P
            if !isempty(l1)
                isempty(l2) && return false
                x,y = l1[1],l2[1]
                return R((x,y),h) && pw(l1[2:end],l2[2:end],h)
            end
            isempty(l2) && return true 
            return false
        end
        new("PAIRWISE",pw,[R])
    end
end

export ALLPARTS

ALLPARTS(P::CPROP) = PARTS(ALL(P))

export SOMEPART

SOMEPART(P::CPROP) = PARTS(SOME(P))

export FIRSTPART

FIRSTPART(P::Union{CPROP,Id}) = PARTS(FIRST(P))

export LASTPART

LASTPART(P::Union{CPROP,Id}) = PARTS(LAST(P))

export AND

struct AND <: CPROP
    name
    op
    args
    AND(f::CMD,g::CMD) = new("AND",x->h->f(x,h)&&g(x,h),[f,g])
    AND(f::CMD,gs::CMD...) = isempty(gs) ? f : AND(AND(f,gs[1]),gs[2:end]...)
end

export FILTER

struct FILTER <: CMD{List{Id},List{Id}}
    name
    op
    args
    FILTER(P::CPROP) = new("FILTER",l->h->Id[x for x in l if P(x,h)],[P])
end

export SELECT

SELECT(P::CPROP) = BIND(DOM(),FILTER(P))

export PROJ

PROJ(P) = FISH(SUBCS(),FILTER(P))

export SUM

struct SUM <: CMD{List{Number},Number}
    name
    op
    args
    SUM() = new("SUM",l->_->sum(l),[])
end

export AVG

struct AVG <: CMD{List{Number},Float64}
    name
    op
    args
    AVG() = new("AVG",l->_->sum(l)/length(l),[])
end


# SERIALISATION OF QUERIES

export parsedict, loadexpr

using JSON

parsedict(x::Union{JSON.Object,Dict}) = begin
    op = x["op"]
    args = x["args"]
    return eval(Symbol(op))([parsedict(a) for a in args]...)
end
parsedict(x) = eval(Meta.parse(x))

loadexpr(fn::String) = parsedict(JSON.parsefile(fn))

export saveexpr

exprtodict(s::String) = "\"$s\""
exprtodict(x::READ) = Dict(["op"=>x.name,"args"=>[exprtodict(a) for a in x.args]])
exprtodict(x::CMD) = Dict(["op"=>x.name,"args"=>[exprtodict(a) for a in x.args]])
exprtodict(x) = string(x)

saveexpr(fn::String,q::Union{READ,CMD}) = begin 
    D = exprtodict(q)
    open(fn, "w") do f
        JSON.print(f, D)
    end
    return D
end




# VIEWPOINTS

abstract type Viewpoint{T} <: CMD{List{Id},T} end

rt(v::Viewpoint{T}) where T = T

(v::Viewpoint{T})(cs::List{Constituent}) where T = v.op(cs)::Option{T}

struct Atomic{T} <: Viewpoint{T}
    name
    args
    rts
    op
    Atomic(a::Attribute{N,T}) where {N,T} = begin 
        name = "Atomic"
        args = [a]
        rts = [T]
        function op(ids::List{Id},h::Union{Hierarchy,Module,Graph})
            return obind(peeklast(ids),x->geta(a,x,h))
        end
        function op(cs::List{Constituent})
            return obind(peeklast(cs),c->geta(a,c))
        end
        return new{T}(name,args,rts,op)
    end
    Atomic(a::Union{Symbol,String}) = Atomic(__attributes__(a))
end

struct Linked{T} <: Viewpoint{T}
    name
    args
    rts
    op
    Linked(v1::Viewpoint,v2::Viewpoint,vs::Viewpoint...) = begin
        name = "Linked"
        args = [v1,v2,vs...]
        rts = rt.([v1,v2,vs...])
        function op(ids::List{Id},h::Union{Hierarchy,Module,Graph})
            res = [v(ids,h) for v in args]
            none in res && return none
            return Tuple(res)
        end
        function op(cs::List{Constituent})
            res = [v(cs) for v in args]
            none in res && return none
            return Tuple(res)
        end
        new{Tuple{rts...}}(name,args,rts,op)
    end
end

struct Derived{T} <: Viewpoint{T}
    name
    args
    rts
    op
    Derived(v::Viewpoint,f::Function) = begin
        name = "Derived"
        args = [v,string(f)]
        T = Base._return_type(f,Tuple{v.rts...})
        T == Union{} && error("Cannot compose $f with $v .")
        rts = [T]
        function op(ids::List{Id},h::Union{Hierarchy,Module,Graph})
            n = length(v.rts)
            n == 1 ? obind(v(ids,h),f) : obind(v(ids,h),x->f(x...))
        end
        function op(cs::List{Constituent})
            n = length(v.rts)
            n == 1 ? obind(v(cs),f) : obind(v(cs),x->f(x...))
        end
        new{T}(name,args,rts,op)
    end
end

struct Delayed{T} <: Viewpoint{T}
    name
    args
    rts
    op
    Delayed(v::Viewpoint{T},l::Int) where T = begin
        name = "Delayed"
        args = [v,l]
        rts = v.rts
        function op(ids::List{Id},h::Union{Hierarchy,Module,Graph})
            return v(droplast(ids,l),h)
        end
        function op(cs::List{Constituent})
            return v(droplast(cs,l))
        end
        return new{T}(name,args,rts,op)
    end
end

struct Threaded{T} <: Viewpoint{T}
    name
    args
    rts
    op
    Threaded(base::Viewpoint{T},test::Viewpoint{Bool}) where T = begin
        name = "Threaded"
        args = [base,test]
        rts = base.rts
        function op(ids::List{Id},h::Union{Hierarchy,Module,Graph})
            return obind(test(ids,h),b-> b ? base(ids,h) : none)
        end
        function op(cs::List{Constituent})
            return obind(test(cs),b-> b ? base(cs) : none)
        end
        return new{T}(name,args,rts,op)
    end
end

struct Position <: Viewpoint{Int}
    name
    args
    rts
    op
    Position() = begin
        name = "Position"
        args = []
        rts = [Int]
        function op(ids::List{Id},h::Union{Hierarchy,Module,Graph})
            return length(ids)
        end
        function op(cs::List{Constituent})
            return length(cs)
        end
        return new(name,args,rts,op)
    end
end

struct Since <: Viewpoint{Int}
    name
    args
    rts
    op
    Since(v::Viewpoint{Bool}) = begin
        name = "Since"
        args = [v]
        rts = [Int]
        function op(ids::List{Id},h::Union{Hierarchy,Module,Graph})
            loc = findlast(vpmap(v,ids,h))
            loc == nothing && return length(ids)
            return length(ids)-loc
        end
        function op(cs::List{Constituent})
            loc = findlast(vpmap(v,cs))
            loc == nothing && return length(cs)
            return length(cs)-loc
        end
        return new(name,args,rts,op)
    end
end

# VIEWPOINT CONSTRUCTOR INTERFACE

export vp

vp(x::Attribute) = Atomic(x)

export atomic

atomic(x::Union{Attribute,Symbol,String}) = Atomic(x)

export link

link(v1::Viewpoint,v2::Viewpoint,vs::Viewpoint...) = Linked(v1,v2,vs...)

export compose

compose(v::Viewpoint,f::Function) = Derived(v,f)

export delay

delay(v::Viewpoint,l::Int) = Delayed(v,l)

export thread

thread(b::Viewpoint,t::Viewpoint) = Threaded(b,t)

export position

position() = Position()

export since

since(v::Viewpoint) = Since(v)

# DIFFERENTIATE VIEWPOINTS

export diff, difflin, diffrat

diff(v::Viewpoint, op::Function) = compose(link(v,delay(v,1)),op)
difflin(v::Viewpoint) = diff(v,(x,y)->x-y)
diffrat(v::Viewpoint) = diff(v,(x,y)->x/y)
diff(v::Viewpoint) = difflin(v)
diff(v::Viewpoint,s::String) = begin
    if s == "Ratio"
        return diffrat(v)
    elseif op == "Linear"
        return difflin(v)
    else
        println("Error: Operator name is not available. You can take a look to the list of available operators.")
        println("Helper")
        println("------------------")
        println("2- Ratio")
        println("3- Linear")
        println("------------------")
    end
end


# MAP VIEWPOINTS OVER A SEQUENCE

export vpmap, vp_map

vpmap(v::Viewpoint{T},cs::List{Constituent}) where T = @views Option{T}[v(cs[1:n]) for n in 1:length(cs)]
vpmap(v::Viewpoint{T},ids::List{Id},h::Union{Hierarchy,Module,Graph}) where T = @views Option{T}[v(ids[1:n],h) for n in 1:length(ids)]

# keep backwards compatibility
vp_map = vpmap



end # module
