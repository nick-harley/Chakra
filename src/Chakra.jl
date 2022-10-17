module Chakra

export List
export nil, cons, isnil, list_rec, gethead, gettail, append, lmap, ljoin, lpush, lpop, lpopn, lpeek, lpeekn


export Option
export none, option_rec, omap, obind


export agg, pts, geta, seta, getp, setp, emp, ins, rmv, pop, peek, fnd, isemp, mem, dom, cts
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

function list_rec(::Type{T},pnil::T,pcons::Function,x::Vector{E})::T where {T,E} 
    function F(l)
        isnil(l) ? pnil : pcons(l[1],l[2:end],F(l[2:end]))
    end
    return F(x)
end

function gethead(l::List{A})::Option{A} where A 
    list_rec(Option{A},none,(h,t,r)->h,l)
end
function gettail(l::List{A})::List{A} where A
    list_rec(List{A},nil(A),(h,t,r)->t,l)
end
function append(l1::List{A},l2::List{A})::List{A} where A
    list_rec(List{A},l2,(h,t,r)->cons(h,r),l1)
end
function lmap(f::Function,l::List{A})::List{B} where {A,B}
    list_rec(List{B},nil(B),(h,t,r)->cons(f(h),r),l)
end
function ljoin(ll::List{List{A}})::List{A} where A
    list_rec(List{A},nil(A),(h,t,r)->append(h,r),ll)
end
function lpush(l::List{A},x::A)::List{A} where A
    list_rec(List{A},cons(x,nil(A)),(h,t,r)->cons(h,r),l)
end
function lpop(l::List{A})::List{A} where A
    list_rec(List{A},nil(A),(h,t,r)->isnil(t) ? r : cons(h,r),l)
end
function lpopn(l::List{A},n::Int)::List{A} where A
    n <= 0 ? l : lpopn(lpop(l),n-1)
end
function lpeek(l::List{A})::Option{A} where A
    list_rec(Option{A},none,(h,t,r)->isnil(t) ? h : r,l)
end
function lpeekn(l::List{A},n::Int)::Option{A} where A
    lpeek(lpopn(l,n))
end





# ABSTRACT TYPES

abstract type Id end

abstract type Constituent end

abstract type Hierarchy end

abstract type Attribute{a,T} end

abstract type Property{p,T} end




# GLOBAL ATTRIBUTES AND PROPERTIES

function __attributes__(::Val{n})::Attribute{n} where n
    error("Name $n is not defined globally.")
end
__attributes__(n::Symbol) = __attributes__(Val{n}())
__attributes__(n::String) = __attributes__(Symbol(n))


function __properties__(::Val{n})::Property{n} where n
    error("Name $n is not defined globally.")
end
__properties__(n::Symbol) = __properties__(Val{n}())
__properties__(n::String) = __properties__(Symbol(n))




# ERROR FUNCTION        

function Error(name,TS...)
    type_string = string(join(string.(typeof.(TS[1:end-1]))," -> ")," -> ",TS[end])
    error(string("No method implementation of $name : ", type_string, ". \n $(methods(name))"))
end




# ABSTRACT OPERTIONS


## Constituent constructors 

function agg(ps::List{T})::Constituent where {T<:Id}

    # agg : list Id -> Constituent

    Error(agg,ps,Constituent)

end 

function seta(a::Attribute{N,T},
              v::T,
              c::Constituent)::Constituent where {N,T}

    # forall a::A, typ a -> Constituent -> Constituent

    Error(seta,a,v,c,Constituent)
end

function setp(p::Property{N,T},
              v::T,
              c::Constituent)::Constituent where {N,T}

    # forall p::P, T -> Constituent -> Constituent

    Error(setp,p,v,c,Constituent)
end


## Constituent destructors

function geta(a::Attribute{N,T},
              c::Constituent)::Option{T} where {N,T}

    # forall a::A, Constituent -> option (typ a)

    Error(geta,a,c,Option{T})
end

function getp(p::Property{N,T},
              c::Constituent)::Option{T} where {N,T}

    # forall p::P, Constituent -> option (typ p)

    Error(getp,p,c,Option{T})
end

function pts(c::Constituent)::List{Id}
    
    # pts : Constituent -> list Id

    Error(pts,c,List{Id})
end


## Hierarchy constructors

function emp(::Type{Hierarchy})::Hierarchy

    # emp : H

    Error(emp,Hierarchy,Hierarchy)
end

function ins(x::Id,
             c::Constituent,
             h::Hierarchy)::Hierarchy

    # ins : Id -> Constituent -> Hierarchy -> Hierarchy

    Error(ins,x,c,h,Hierarchy)
end 

function rmv(x::Id,
             h::Hierarchy)::Hierarchy

    # rmv : Id -> H -> H

    Error(rmv,x,h,Hierarchy)
end

function pop(h::Hierarchy)::Hierarchy

    # pop : Hierarchy -> Hierarchy

    Error(pop,h,Hierarchy)
end


## Hierarchy destructors

function fnd(x::Id,
             h::Hierarchy)::Option{Constituent}

    # fnd : Id -> Hierarchy -> option Constituent

    Error(fnd,x,h,Option{Constituent})
end

function peek(h::Hierarchy)::Option{Pair{Id,Constituent}}

    # peek : Hierarchy -> option (Id * Constituent)

    Error(peek,h,Option{Pair{Id,Constituent}})
end

function cts(h::Hierarchy)::List{Pair{Id,Constituent}}

    # cts : Hierarchy -> list (Id * C)

    Error(cts,h,List{Pair{Id,Constituent}})
end

function dom(h::Hierarchy)::List{Id}
    
    # dom : Hierarchy -> list Id

    Error(dom,h,List{Id})
end


## Boolean tests

function isemp(h::Hierarchy)::Bool
    
    # isemp : Hierarchy -> bool 

    Error(isemp,h,Bool)
end

function mem(x::Id,
             h::Hierarchy)::Bool
    
    # mem : Id -> Hierarchy -> bool

    Error(mem,x,h,Bool)
end



# ADDITIONAL METHODS


# constituent constructors
agg(::Type{T}) where {T<:Id} = agg(T[])

agg(ps::Vector{Id}) = agg(Union{typeof.(ps)...}[ps...])

seta(a::String,v,c::Constituent) = seta(__attributes__(a),v,c)

setp(p::String,v,c::Constituent) = setp(__properties__(p),v,c)

seta(a,v,x,h) = obind(fnd(x,h),c->seta(a,v,c))

setp(p,v,x,h) = obind(fnd(x,h),c->setp(p,v,c))

# constituent destructors
pts(x::Id,h) = obind(fnd(x,h),c->pts(c))

geta(a::String,c::Constituent) = geta(__attributes__(a),c)

getp(p::String,c::Constituent) = getp(__properties__(p),c)

geta(a,x::Id,h) = obind(fnd(x,h),c->geta(a,c))

getp(p,x::Id,h) = obing(fnd(x,h),c->getp(p,c))

# hierarchy destructors
fnd(x::Id,m::Module) = fnd(x,m.__data__)

dom(m::Module) = dom(m.__data__)

cts(m::Module) = cts(m.__data__)

peek(m::Module) = peek(m.__data__)

# boolean tests
mem(x,m::Module) = mem(x,m.__data__)

isemp(m::Module) = isemp(m.__data__)

# mapping functions
function sequence(xs::List{X},h::Hierarchy)::Option{List{Constituent}} where {X<:Id}

    # Dereference the list of ids to get their constituents
    
    list_rec(Option{List{Constituent}},nil(Constituent),
             (hd,tl,rec)->obind(fnd(hd,h),
                                c->obind(rec,l->cons(c,l))),
             xs)
end

function sequence(x::Id,h::Hierarchy)

    # Dereference the particles of a constituent

    obind(pts(x,h),ps->sequence(ps,h))
    
end

sequence(x,m::Module) = sequence(x,m.__data__)




# REFERENCE IMPLEMENTATION MACRO

macro Reference(Id,SUBS=[])
    
    esc(quote
            
            struct Id <: Chakra.Id
                value::($Id)
            end

            __IDS__ = Union{Id,[s.__IDS__ for s in $SUBS]...}
            
            As = Dict{Symbol,Any}
            Ps = Dict{Symbol,Any}
            Parts = List{__IDS__}
            
            struct Constituent <: Chakra.Constituent
                attributes::As
                properties::Ps
                particles::Parts
            end

            __CS__ = Union{Constituent,[s.__CS__ for s in $SUBS]...}

            using DataStructures

            Cs = OrderedDict{Id,Constituent}
            
            struct Hierarchy <: Chakra.Hierarchy
                constituents::Cs
            end

            mod = @__MODULE__

            __attributes__(::Val{a}) where a =
                error("Attribute $a is not defined in module $mod.")

            __attributes__(a::Symbol)::Type = __attributes__(Val{a}())

            struct Attribute{a,T} <: Chakra.Attribute{a,T}
                Attribute(a::Symbol) = new{a,__attributes__(a)}()
            end

            macro DefineAttribute(a,T) 
                esc(quote
                        __attributes__(::Val{$a}) = $T
                        g = Symbol(@__MODULE__,".",$a)
                        Chakra.__attributes__(::Val{g}) = Attribute($a)
                    end)
            end

            __properties__(::Val{p}) where p =
                error("Property $p is not defined in module $mod.")

            __properties__(p::Symbol)::Type = __properties__(Val{p}())

            struct Property{p,T} <: Chakra.Property{p,T}
                Property(p::Symbol) = new{p,__properties__(p)}()
            end

            macro DefineProperty(p,T)    
                esc(quote
                        mod.__properties__(::Val{$p}) = $T
                        g = Symbol(mod,".",$p)
                        Chakra.__properties__(::Val{g}) = Property($p)
                    end)
            end
            
            Chakra.agg(ps::List{T}) where T<:__IDS__ =
                Constituent(As(),Ps(),ps)

            Chakra.agg(::Type{Constituent}) = agg(__IDS__[])

            Chakra.seta(::Attribute{a,T},
                        v::T,
                        c::Constituent) where {a,T} =
                            Constituent(As(c.attributes...,a=>v),
                                        Ps(c.properties),
                                        c.particles)

            Chakra.seta(a::Symbol,v,c) = Chakra.seta(Attribute(a),v,c)
            
            Chakra.setp(::Property{p,T},
                        v::T,
                        c::Constituent) where {p,T} =
                            Constituent(As(c.attributes),
                                        Ps(c.properties...,p=>v),
                                        c.particles)

            Chakra.setp(p::Symbol,v,c) = Chakra.setp(Property(p),v,c)
            
            Chakra.pts(c::Constituent)::List{__IDS__} =
                c.particles

            Chakra.geta(::Attribute{a,T},
                        c::Constituent) where {a,T} =
                            Base.get(c.attributes,a,none)

            Chakra.geta(a::Symbol,
                        c::Constituent) =
                            Chakra.geta(Attribute(a),c)
            
            Chakra.getp(::Property{p,T},
                        c::Constituent) where {p,T} =
                            Base.get(c.properties,p,none)

            Chakra.getp(p::Symbol,
                        c::Constituent) =
                            Chakra.getp(Property(p),c)
            
            Chakra.emp(::Type{Hierarchy})::Hierarchy =
                Hierarchy(Cs())

            Chakra.ins(x::Id,
                       c::Constituent,
                       h::Hierarchy)::Hierarchy =
                           Hierarchy(Cs(h.constituents..., x => c))

            Chakra.rmv(x::Id,
                       h::Hierarchy)::Hierarchy =
                           Hierarchy(delete!(Cs(h.constituents),x))
            
            Chakra.pop(h::Hierarchy)::Hierarchy =
                Hierarchy(Cs(collect(h.constituents)[1:end-1]))

            Chakra.fnd(x::Id,
                       h::Hierarchy)::Option{Constituent} =
                           Base.get(h.constituents,x,none)

            for S in $SUBS
                eval(:(Chakra.fnd(x::$S.Id,h::Hierarchy)::$S.Constituent = fnd(x,$S.__data__)))
            end
            
            Chakra.peek(h::Hierarchy)::Option{Pair{__IDS__,__CS__}} =
                cts(h)[1]

            Chakra.isemp(h::Hierarchy)::Bool =
                isempty(dom(h))

            Chakra.mem(x::Id,h::Hierarchy)::Bool =
                haskey(h.constituents,x)

            for S in $SUBS
                eval(:(Chakra.mem(x::$S.Id,h::Hierarchy)::Bool = mem(x,$S.__data__)))
            end
            
            Chakra.cts(h::Hierarchy)::List{Pair{__IDS__,__CS__}} =
                vcat(reverse(collect(h.constituents)),[cts(S.__data__) for S in reverse($SUBS)]...)

            Chakra.dom(h::Hierarchy)::List{__IDS__} =
                vcat(reverse(collect(keys(h.constituents))),[dom(S.__data__) for S in reverse($SUBS)]...)

        end)
end



# META OPERATIONS

function isdatasource(m::Module)
    isdefined(m,:__data__) && m.__data__ isa Hierarchy
end




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

vp(x::Attribute) = AtomicViewpoint(x)

link(v1::Viewpoint,v2::Viewpoint,vs::Viewpoint...) = LinkedViewpoint(v1,v2,vs...)

compose(v::Viewpoint,f::Function) = DerivedViewpoint(v,f)

delay(v::Viewpoint,l::Int) = DelayedViewpoint(v,l)

thread(b::Viewpoint,t::Viewpoint) = ThreadedViewpoint(b,t)

# Additional viewpoint constructors

diff(v::Viewpoint{T}) where T = compose(link(v,delay(v,1)),(x,y)->x-y)

# isdiffable(v::Viewpoint{T}) where T = TODO : how to check whether T has a "-"


function vp_map(v::Viewpoint{T},s::Vector)::List{Option{T}} where T

    # Maps a viewpoint of a sequence

    return [v(s[1:n]) for n in 1:length(s)]
end



end # module
