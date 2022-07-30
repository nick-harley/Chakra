module Chakra

export List
export nil, cons, isnil, list_rec, gethead, gettail, append, lmap, ljoin, lpush, lpop, lpopn, lpeek, lpeekn


export Option
export none, option_rec, omap, obind


export Att

export agg, pts, geta, seta, emp, ins, rmv, pop, peek, fnd, isemp, mem, dom, cts
export sequence


export Viewpoint
export vp, link, compose, delay, thread, diff, vp_map


# OPTION

struct None end
none = None()
some(x::A) where A = a

Option{A} = Union{A,None}

function option_rec(pnone,psome::Function,x::Option{A}) where A
    x isa None ? pnone : psome(x)
end

omap(f::Function,x::Option{A}) where A = option_rec(none,f,x)

obind(x::Option{A},f::Function) where A = option_rec(none,f,x)







# LIST

List{T} = Vector{T}

nil(::Type{T}) where T = T[]
nil() = Any[]
cons(h::T,t::List{T}) where T = T[h,t...]
isnil(l::List) = isempty(l)

function list_rec(pnil,pcons::Function,x::Vector) 
    function F(l)
        isnil(l) ? pnil : pcons(l[1],l[2:end],F(l[2:end]))
    end
    return F(x)
end

function gethead(l::List{A})::Option{A} where A 
    list_rec(none,(h,t,r)->h,l)
end
function gettail(l::List{A})::List{A} where A
    list_rec(nil(A),(h,t,r)->t,l)
end
function append(l1::List{A},l2::List{A})::List{A} where A
    list_rec(l2,(h,t,r)->cons(h,r),l1)
end
function lmap(f::Function,l::List{A})::List where A
    list_rec(nil(),(h,t,r)->cons(f(h),r),l)
end
function ljoin(ll::List{List{A}})::List{A} where A
    list_rec(nil(A),(h,t,r)->append(h,r),ll)
end
function lpush(l::List{A},x::A)::List{A} where A
    list_rec(cons(x,nil(A)),(h,t,r)->cons(h,r),l)
end
function lpop(l::List{A})::List{A} where A
    list_rec(nil(A),(h,t,r)->isnil(t) ? r : cons(h,r),l)
end
function lpopn(l::List{A},n::Int)::List{A} where A
    n <= 0 ? l : lpopn(lpop(l),n-1)
end
function lpeek(l::List{A})::Option{A} where A
    list_rec(none,(h,t,r)->isnil(t) ? h : r,l)
end
function lpeekn(l::List{A},n::Int)::Option{A} where A
    lpeek(lpopn(l,n))
end








# DEPENDENT FAMILIES

__typ__(::Val{a}) where a = error("The attribute name $a has not been associated with a type.")

__typ__(n::Symbol)::DataType = __typ__(Val{n}())

macro Attribute(n,T)    
    esc(:(Chakra.__typ__(::Val{$n}) = $T))
end

struct Att{a,T}
    a::Symbol
    T::DataType
    Att(a::Symbol) = begin
        T = __typ__(a)
        new{a,T}(a,T)
    end
end

        
        
# INTERFACE FUNCTIONS        

function agg(ps::List{ID}) where ID
    error("No implementation of agg.")
end

function pts(c::C) where C
    error("No implementation of pts.")
end

function geta(::Att{a,T},c::C) where {a,T,C}
    error("No implementation of geta.")
end

function seta(::Att{a,T},v::T,c::C) where {a,T,C}
    error("No implementation of seta.")
end
# TODO: Add properties

function emp(T::DataType)
    error("No implementation of emp.")
end

function ins(x::ID,c::C,h::H) where {ID,C,H}
    error("No implementation of ins.")
end

function rmv(x::ID,h::H) where {ID,H}
    error("No implementation of rmv.")
end

function pop(h::H) where {H}
    error("No implementation of rmv.")
end

function fnd(x::ID,h::H) where {ID,H}
    error("No implementation of fnd.")
end

function peek(h::H) where {H}
    error("No implementation of peek.")
end

function isemp(h::H) where {H}
    error("No implementation of isemp.")
end
function mem(x::ID,h::H) where {ID,H}
    error("No implementation of mem.")
end

function cts(h::H) where H
    error("No implementation of cts.")
end

function dom(h::H) where H
    error("No implementation of dom.")
end

# IMPERATIVE OPERATION

function ins!(x::ID,c::C,h::H) where {ID,C,H}
    error("No implementation of insert!.")
end

function seta!(::Att{a,T},v::T,c::C) where {a,T,C}
    error("No implementation of setatt!.")
end

# ADDITIONAL OPERATIONS

agg(ID::DataType) = agg(ID[])

pts(x,h) = obind(fnd(x,h),c->pts(c))

geta(a::Symbol,c) = geta(Att(a),c)

geta(a::Symbol,x,h) = obind(fnd(x,h),c->geta(a,c))

seta(a::Symbol,v,c) = seta(Att(a),v,c)

seta!(a::Symbol,v,c) = seta!(Att(a),v,c)

seta(a,v,x,h) = obind(fnd(x,h),c->seta(a,v,c))

seta!(a,v,x,h) = obind(fnd(x,h),c->seta!(a,v,c))
                
function sequence(xs::List{ID},h::H)::Option{List} where {ID,H}

    # Dereference the list of ids to get their objects
    
    list_rec(nil(),
             (hd,tl,rec)->obind(fnd(hd,h),
                                c->obind(rec,l->cons(c,l))),
             xs)
end

function sequence(x::ID,h::H)::Option{List} where {ID,H}

    # Dereference the particles of a constituent

    obind(pts(x,h),ps->sequence(ps,h))
    
end




abstract type Viewpoint{T} end

returntype(v::Viewpoint{T}) where T = T

struct AtomicViewpoint{T} <: Viewpoint{T}
    attribute::Symbol
    returntypes::List{DataType}
    AtomicViewpoint(a::Symbol) = new{__typ__(a)}(a,[__typ__(a)])
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
        t = Base._return_type(f,Tuple(v.returntypes))
        if t == Union{}
            error("Type mismatch: The function $f is not composable with the viewpoint $v")
        end
        new{t}(v,f)
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

vp(x::Symbol) = AtomicViewpoint(x)

link(v1::Viewpoint,v2::Viewpoint,vs::Viewpoint...) = LinkedViewpoint(v1,v2,vs...)

compose(v::Viewpoint,f::Function) = DerivedViewpoint(v,f)

delay(v::Viewpoint,l::Int) = DelayedViewpoint(v,l)

thread(b::Viewpoint,t::Viewpoint) = ThreadedViewpoint(b,t)



# Additional viewpoint constructors

diff(v::Viewpoint{T}) where T = compose(link(v,delay(v,1)),(x,y)->x-y)




function vp_map(v::Viewpoint{T},s::Vector)::List{Option{T}} where T

    # Maps a viewpoint of a sequence

    return [v(s[1:n]) for n in 1:length(s)]
end



end # module
