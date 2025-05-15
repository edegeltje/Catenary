import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sets.OpenCover
import Catenary.RelSeriesHT.Defs
import Catenary.RelSeriesHT.Codim
import Catenary.Order.Defs

open TopologicalSpace Rel RelSeriesHT ENat

namespace TopologicalSpace

variable (X : Type) [TopologicalSpace X]

notation "∞" => ⊤

abbrev IsCatenaryTopologicalSpace := IsCatenaryOrder (IrreducibleCloseds X)
abbrev IsIrreduciblyNoetherianTopologicalSpace := IsDiscreteOrder (IrreducibleCloseds X)

/--
A topological space is irreducibly Noetherian if and only if the irreducibles satisfy the descending chain condition.
-/
lemma irreducibly_noetherian_iff_codim_lt_infty : IsIrreduciblyNoetherianTopologicalSpace X ↔ ∀ Y Y' : IrreducibleCloseds X, eCodim Y Y' < ∞ := RelSeriesHT.isDiscrete_iff_forall_eCodim_lt_top

/--
A topological space is catenary if and only if it is irreducibly Noetherian and satisfies the dimension formula.
-/
@[stacks 02I6]
lemma catenary_iff_dimension_formula : IsCatenaryTopologicalSpace X ↔ IsIrreduciblyNoetherianTopologicalSpace X ∧ ∀ Y Y' Y'' : IrreducibleCloseds X, Y < Y' → Y' < Y'' → eCodim Y Y' + eCodim Y' Y'' = eCodim Y Y'' := isCatenaryOrder_iff_isDiscreteOrder_and_dimension_formula (IrreducibleCloseds X)

end TopologicalSpace
