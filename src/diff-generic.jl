# Function authored by Ardavan Khalij, https://github.com/ArdavanKhalij

Chakra.diff(v::Viewpoint{T}, op::String) where T = apply_diff(v::Viewpoint{T}, op::String)

function apply_diff(v::Viewpoint{T}, op::String) where T
    if op == "Ratio"
        return compose(link(v,delay(v,1)),(x,y)->y/x)
    elseif op == "Linear"
        return compose(link(v,delay(v,1)),(x,y)->x-y)
    else
        println("Error: Operator name is not available. You can take a look to the list of available operators.")
        println("Helper")
        println("------------------")
        println("2- Ratio")
        println("3- Linear")
        println("------------------")
    end
end
