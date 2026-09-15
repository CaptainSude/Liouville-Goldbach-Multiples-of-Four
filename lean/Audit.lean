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

#check Shusterman.shusterman_positive_multiples_of_four
#print axioms Shusterman.reflection_of_no_positive_pair
#print axioms Shusterman.not_hasPositivePair_four
#print axioms Shusterman.shusterman_positive_multiples_of_four

/-- info: 'Shusterman.reflection_of_no_positive_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shusterman.reflection_of_no_positive_pair

/-- info: 'Shusterman.shusterman_positive_multiples_of_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shusterman.shusterman_positive_multiples_of_four

/-- info: 'Shusterman.negativePair_four_mul_of_equalPair_golfed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shusterman.negativePair_four_mul_of_equalPair_golfed
