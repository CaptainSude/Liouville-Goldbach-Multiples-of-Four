import Shusterman

-- Print the theorem type as well as its logical axioms: the explicit
-- Mangerel hypothesis remains visible even though it is not an axiom.
#check Shusterman.shusterman_multiples_of_four
#print Shusterman.MangerelNonextremality
#print axioms Shusterman.reflection_of_no_negative_pair
#print axioms Shusterman.MangerelNonextremality.equalPair
#print axioms Shusterman.shusterman_multiples_of_four

-- This regression check fails if the final proof acquires another logical
-- axiom, including `sorryAx`. It does not discharge the explicit input hM.
/-- info: 'Shusterman.shusterman_multiples_of_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shusterman.shusterman_multiples_of_four
