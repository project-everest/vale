module Math__power_s {

function {:opaque} power(b:int, e:nat) : int
    decreases e;
{
    if (e==0) then
        1
    else
        b*power(b,e-1)
}

} 
