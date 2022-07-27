module Chakra

export List
export nil, cons, isnil, list_rec, gethead, gettail, append, lmap, ljoin, lpush, lpop, lpopn, lpeek, lpeekn


export Option
export none, option_rec, omap, obind


export Att

export sequence



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


function delimit(ps::List{Id}) where Id
    error("No implementation of delimit.")
end
function particles(o::Obj) where Obj
    error("No implementation of particles.")
end
function getatt(::Att{a,T},o::Obj) where {a,T,Obj}
    error("No implementation of getatt.")
end
function setatt(::Att{a,T},v::T,o::Obj) where {a,T,Obj}
    error("No implementation of setatt.")
end
function empty(T::DataType)
    error("No implementation of empty.")
end
function insert(x::Id,o::Obj,s::Str) where {Id,Obj,Str}
    error("No implementation of insert.")
end
function find(x::Id,s::Str) where {Id,Str}
    error("No implementation of find.")
end
function domain(s::Str) where Str
    error("No implementation of domain.")
end

# Persistent structures

function insert!(x::Id,o::Obj,s::Str) where {Id,Obj,Str}
    error("No implementation of insert!.")
end
function setatt!(::Att{a,T},v::T,o::Obj) where {a,T,Obj}
    error("No implementation of setatt!.")
end

# ADDITIONAL OPERATIONS

delimit(Id::DataType) = delimit(Id[])

particles(x,s) = obind(find(x,s),o->particles(o))

getatt(a::Symbol,o) = getatt(Att(a),o)

getatt(a::Symbol,x,s) = obind(find(x,s),o->getatt(a,o))

setatt(a::Symbol,v,o) = setatt(Att(a),v,o)

setatt!(a::Symbol,v,o) = setatt!(Att(a),v,o)

function sequence(xs::List,s)::Option{List}

    # Dereference the list of ids to get their objects
    
    list_rec(nil(),(h,t,r)->obind(find(h,s),o->obind(r,rec->cons(o,rec))),xs)
end

function sequenceparts(x,s)::Option{List}

    # Dereference the particles of an object

    obind(particles(x,s),xs->sequence(xs,s))
    
end



end # module
