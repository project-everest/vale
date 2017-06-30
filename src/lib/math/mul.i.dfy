include "mul_nonlinear.i.dfy"
include "mul_auto.i.dfy"

module Math__mul_i {
import opened Math__mul_nonlinear_i
import opened Math__mul_auto_i

function mul(x:int, y:int) : int { x*y }

//-////////////////////////////////////////////////////////////
//- Recursive definitions that can be handy for proving 
//- properties we can't or don't want to rely on nonlinear for
//-////////////////////////////////////////////////////////////

function mul_recursive(x:int, y:int) : int
{
 if x >= 0 then mul_pos(x, y)
 else -1*mul_pos(-1*x, y)
}

function{:opaque} mul_pos(x:int, y:int) : int
 requires x >= 0;
{
 if x == 0 then 0
 else y + mul_pos(x - 1, y)
}

lemma lemma_mul_is_mul_recursive(x:int, y:int)
    ensures x * y == mul_recursive(x, y);
{
    if (x >= 0) { lemma_mul_is_mul_pos(x, y); }
    if (x <= 0) { lemma_mul_is_mul_pos(-x, y); }
    lemma_mul_auto();
}

lemma lemma_mul_is_mul_pos(x:int, y:int)
    requires x >= 0;
    ensures x * y == mul_pos(x, y);
{
    reveal_mul_pos();
    lemma_mul_auto_induction(x, imap u :: u >= 0 ==> u * y == mul_pos(u, y));
}

//-////////////////////////////////////////////////////////////////////////////
//-
//- Core lemmas, with named arguments.
//-
//-////////////////////////////////////////////////////////////////////////////

lemma lemma_mul_basics(x:int)
    ensures 0*x == 0;
    ensures x*0 == 0;
    ensures 1*x == x;
    ensures x*1 == x;
{
}

lemma lemma_mul_is_commutative(x:int, y:int)
    ensures x*y == y*x;
{
}

lemma lemma_mul_ordering_general()
    ensures forall x:int, y:int {:trigger x*y} :: (0 < x && 0 < y && 0 <= x*y) ==> x <= x*y && y <= x*y;
{
    forall x:int, y:int | 0 < x && 0 < y && 0 <= x*y
        ensures x <= x*y && y <= x*y;
    {
        lemma_mul_ordering(x, y);
    }
}

lemma lemma_mul_is_mul_boogie(x:int, y:int)
{
}

lemma lemma_mul_inequality(x:int, y:int, z:int)
    requires x <= y;
    requires z >= 0;
    ensures  x*z <= y*z;
{
    lemma_mul_auto_induction(z, imap u :: u >= 0 ==> x * u <= y * u);
}

lemma lemma_mul_upper_bound(x:int, x_bound:int, y:int, y_bound:int)
    requires x <= x_bound;
    requires y <= y_bound;
    requires 0<=x;
    requires 0<=y;
    ensures x*y <= x_bound * y_bound;
{
    lemma_mul_inequality(x, x_bound, y);
    lemma_mul_inequality(y, y_bound, x_bound);
}

//- This lemma is less precise than the non-strict version, since
//- it uses two < facts to achieve only one < result. Thus, use it with
//- caution -- it may be throwing away precision you'll require later.
lemma lemma_mul_strict_upper_bound(x:int, x_bound:int, y:int, y_bound:int)
    requires x < x_bound;
    requires y < y_bound;
    requires 0<=x;
    requires 0<=y;
    ensures x*y < x_bound * y_bound;
{
    lemma_mul_auto_induction(x, imap u :: 0 <= u ==> u * y <= u * y_bound);
    lemma_mul_auto_induction(y_bound, imap u :: 1 <= u ==> x * u < x_bound * u);
}

lemma lemma_mul_left_inequality(x:int, y:int, z:int)
    requires x > 0;
    ensures y <= z ==> x*y <= x*z;
    ensures y < z ==> x*y < x*z;
{
    lemma_mul_auto_induction(x, imap u :: u > 0 ==> y <= z ==> u*y <= u*z);
    lemma_mul_auto_induction(x, imap u :: u > 0 ==> y < z ==> u*y < u*z);
}

lemma lemma_mul_strict_inequality_converse(x:int, y:int, z:int)
    requires x*z < y*z;
    requires z >= 0;
    ensures  x < y;
{
    lemma_mul_auto_induction(z, imap u :: x * u < y * u && u >= 0 ==> x < y);
}

lemma lemma_mul_inequality_converse(x:int, y:int, z:int)
    requires x*z <= y*z;
    requires z > 0;
    ensures  x <= y;
{
    lemma_mul_auto_induction(z, imap u :: x * u <= y * u && u > 0 ==> x <= y);
}

lemma lemma_mul_equality_converse(x:int, y:int, z:int)
    requires x*z == y*z;
    requires 0<z;
    ensures x==y;
{
    lemma_mul_auto_induction(z, imap u :: x > y && 0 < u ==> x * u > y * u);
    lemma_mul_auto_induction(z, imap u :: x < y && 0 < u ==> x * u < y * u);
}

lemma lemma_mul_is_distributive_add_other_way(x:int, y:int, z:int)
    ensures (y + z)*x == y*x + z*x;
{
    lemma_mul_auto();
}

lemma lemma_mul_is_distributive_sub(x:int, y:int, z:int)
    ensures x*(y - z) == x*y - x*z;
{
    lemma_mul_auto();
}

lemma lemma_mul_is_distributive(x:int, y:int, z:int)
    ensures x*(y + z) == x*y + x*z;
    ensures x*(y - z) == x*y - x*z;
    ensures (y + z)*x == y*x + z*x;
    ensures (y - z)*x == y*x - z*x;
    ensures x*(y + z) == (y + z)*x;
    ensures x*(y - z) == (y - z)*x;
    ensures x*y == y*x;
    ensures x*z == z*x;
{
    lemma_mul_auto();
}

lemma lemma_mul_strictly_increases(x:int, y:int)
    requires 1 < x;
    requires 0 < y;
    ensures y < x*y;
{
    lemma_mul_auto_induction(x, imap u :: 1 < u ==> y < u * y);
}

lemma lemma_mul_increases(x:int, y:int)
    requires 0<x;
    requires 0<y;
    ensures y <= x*y;
{
    lemma_mul_auto_induction(x, imap u :: 0 < u ==> y <= u * y);
}

lemma lemma_mul_nonnegative(x:int, y:int)
    requires 0 <= x;
    requires 0 <= y;
    ensures  0 <= x*y;
{
    lemma_mul_auto_induction(x, imap u :: 0 <= u ==> 0 <= u * y);
}

lemma lemma_mul_unary_negation(x:int, y:int)
    ensures (-x)*y == -(x*y) == x*(-y);
{
    lemma_mul_auto_induction(x, imap u :: (-u)*y == -(u*y) == u*(-y));
}

lemma lemma_mul_one_to_one_pos(m:int, x:int, y:int)
    requires 0<m;
    requires m*x == m*y;
    ensures x == y;
{
    lemma_mul_auto_induction(m, imap u :: x > y && 0 < u ==> x * u > y * u);
    lemma_mul_auto_induction(m, imap u :: x < y && 0 < u ==> x * u < y * u);
}

lemma lemma_mul_one_to_one(m:int, x:int, y:int)
    requires m!=0;
    requires m*x == m*y;
    ensures x == y;
{
    lemma_mul_auto_induction(m, imap u :: x > y && 0 < u ==> x * u > y * u);
    lemma_mul_auto_induction(m, imap u :: x > y && 0 > u ==> x * u < y * u);
    lemma_mul_auto_induction(m, imap u :: x < y && 0 < u ==> x * u < y * u);
    lemma_mul_auto_induction(m, imap u :: x < y && 0 > u ==> x * u > y * u);
}

//-////////////////////////////////////////////////////////////////////////////
//-
//- Forall lemmas: these restate the core lemmas with foralls,
//- so callers needn't name the specific expressions to manipulate.
//-
//- These are all boilerplate transformations of args/requires/ensures
//- into forall args :: requires ==> ensures, with a correpsonding
//- mechanically generated forall proof that invokes the core lemma.
//-
//-////////////////////////////////////////////////////////////////////////////

lemma lemma_mul_is_mul_recursive_forall()
    ensures forall x:int, y:int :: x * y == mul_recursive(x, y);
{
    forall x:int, y:int
        ensures x * y == mul_recursive(x, y);
    {
        lemma_mul_is_mul_recursive(x, y);
    }
}

lemma lemma_mul_basics_forall()
    ensures forall x:int {:trigger 0*x} :: 0*x == 0;
    ensures forall x:int {:trigger x*0} :: x*0 == 0;
    ensures forall x:int {:trigger 1*x} :: 1*x == x;
    ensures forall x:int {:trigger x*1} :: x*1 == x;
{
}

lemma lemma_mul_is_commutative_forall()
    ensures forall x:int, y:int {:trigger x*y} :: x*y == y*x;
{
}

lemma lemma_mul_ordering_forall()
    ensures forall x:int, y:int {:trigger x*y} ::
        0 < x && 0 < y && 0 <= x*y
        ==> x <= x*y && y <= x*y;
{
    forall x:int, y:int | 0 < x && 0 < y && 0 <= x*y
        ensures x <= x*y && y <= x*y;
    {
        lemma_mul_ordering(x,y);
    }
}

lemma lemma_mul_strict_inequality_forall()
    ensures  forall x:int, y:int, z:int {:trigger x*z, y*z} ::
        x < y && z>0 ==> x*z < y*z;
{
    forall (x:int, y:int, z:int | x < y && z>0)
        ensures x*z < y*z;
    {
        lemma_mul_strict_inequality(x, y, z);
    }
}

lemma lemma_mul_inequality_forall()
    ensures  forall x:int, y:int, z:int {:trigger x*z, y*z} ::
        x <= y && z>=0 ==> x*z <= y*z;
{
    forall (x:int, y:int, z:int | x <= y && z>=0)
        ensures x*z <= y*z;
    {
        lemma_mul_inequality(x, y, z);
    }
}

lemma lemma_mul_strict_inequality_converse_forall()
    ensures  forall x:int, y:int, z:int {:trigger x*z, y*z} ::
        x*z < y*z && z>=0 ==> x < y;
{
    forall (x:int, y:int, z:int | x*z < y*z && z>=0)
        ensures x < y;
    {
        lemma_mul_strict_inequality_converse(x,y,z);
    }
}

lemma lemma_mul_inequality_converse_forall()
    ensures  forall x:int, y:int, z:int {:trigger x*z, y*z} ::
        x*z <= y*z && z>0 ==> x <= y;
{
    forall (x:int, y:int, z:int | x*z <= y*z && z>0)
        ensures x <= y;
    {
        lemma_mul_inequality_converse(x,y,z);
    }
}

lemma lemma_mul_is_distributive_add_forall()
    ensures forall x:int, y:int, z:int {:trigger x*(y + z)} :: x*(y + z) == x*y + x*z;
{
    forall (x:int, y:int, z:int)
        ensures x*(y + z) == x*y + x*z;
    {
        lemma_mul_is_distributive_add(x,y,z);
    }
}

lemma lemma_mul_is_distributive_sub_forall()
    ensures forall x:int, y:int, z:int {:trigger x*(y - z)} :: x*(y - z) == x*y - x*z;
{
    forall (x:int, y:int, z:int)
        ensures x*(y - z) == x*y - x*z;
    {
        lemma_mul_is_distributive_sub(x,y,z);
    }
}

lemma lemma_mul_is_distributive_forall()
    ensures forall x:int, y:int, z:int {:trigger x*(y + z)} :: x*(y + z) == x*y + x*z;
    ensures forall x:int, y:int, z:int {:trigger x*(y - z)} :: x*(y - z) == x*y - x*z;
    ensures forall x:int, y:int, z:int {:trigger (y + z)*x} :: (y + z)*x == y*x + z*x;
    ensures forall x:int, y:int, z:int {:trigger (y - z)*x} :: (y - z)*x == y*x - z*x;
{
    lemma_mul_is_distributive_add_forall();
    lemma_mul_is_distributive_sub_forall();
    lemma_mul_is_commutative_forall();
}

lemma lemma_mul_is_associative_forall()
    ensures forall x:int, y:int, z:int {:trigger x * (y * z)}{:trigger (x * y) * z} :: x * (y * z) == (x * y) * z;
{
    forall (x:int, y:int, z:int)
        ensures x * (y * z) == (x * y) * z;
    {
        lemma_mul_is_associative(x,y,z);
    }
}

lemma lemma_mul_nonzero_forall()
    ensures forall x:int, y:int {:trigger x*y} :: x*y != 0 <==> x != 0 && y != 0;
{
    forall (x:int, y:int)
        ensures x*y != 0 <==> x != 0 && y != 0;
    {
        lemma_mul_nonzero(x,y);
    }
}

lemma lemma_mul_nonnegative_forall()
    ensures forall x:int, y:int {:trigger x*y} :: 0 <= x && 0 <= y ==> 0 <= x*y;
{
    forall (x:int, y:int | 0 <= x && 0 <= y)
        ensures 0 <= x*y;
    {
        lemma_mul_nonnegative(x,y);
    }
}

lemma lemma_mul_unary_negation_forall()
    ensures forall x:int, y:int {:trigger (-x)*y}{:trigger x*(-y)} :: (-x)*y == -(x*y) == x*(-y);
{
    forall (x:int, y:int) 
        ensures (-x)*y == -(x*y) == x*(-y);
    {
        lemma_mul_unary_negation(x,y);
    }
}

lemma lemma_mul_strictly_increases_forall()
    ensures forall x:int, y:int {:trigger x*y} :: (1 < x && 0 < y) ==> (y < x*y);
{
    forall (x:int, y:int | 1 < x && 0 < y)
        ensures y < x*y;
    {
        lemma_mul_strictly_increases(x,y);
    }
}

lemma lemma_mul_increases_forall()
    ensures forall x:int, y:int {:trigger x*y} :: (0 < x && 0 < y) ==> (y <= x*y);
{
    forall (x:int, y:int | 0 < x && 0 < y)
        ensures y <= x*y;
    {
        lemma_mul_increases(x,y);
    }
}

lemma lemma_mul_strictly_positive_forall()
    ensures forall x:int, y:int {:trigger x*y} :: (0 < x && 0 < y) ==> (0 < x*y);
{
    forall (x:int, y:int | 0 < x && 0 < y)
        ensures 0 < x*y;
    {
        lemma_mul_strictly_positive(x,y);
    }
}

lemma lemma_mul_one_to_one_forall()
    ensures forall m:int, x:int, y:int {:trigger m*x, m*y} :: (m!=0 && m*x == m*y) ==> x==y;
{
    forall (m:int, x:int, y:int | m!=0 && m*x == m*y)
        ensures x==y;
    {
        lemma_mul_one_to_one(m, x, y);
    }
}

lemma lemma_mul_cancels_negatives(a:int, b:int)
    ensures a*b == (-a)*(-b);
{
    lemma_mul_auto();
}

//- Kept for legacy reasons:
function INTERNAL_mul_recursive(x:int, y:int) : int { mul_recursive(x, y) }

} 
