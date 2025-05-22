import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.Constructions
import Mathlib.Topology.IsLocalHomeomorph
import Catenary.RelSeriesHT.Defs
import Catenary.RelSeriesHT.Codim
import Catenary.Order.Defs
import Catenary.Topology.Codim

open TopologicalSpace Rel RelSeriesHT ENat Set Topology Homeomorph

namespace TopologicalSpace

variable (X : Type) [TopologicalSpace X]

notation "∞" => ⊤

abbrev IsCatenaryTopologicalSpace := IsCatenaryOrder (IrreducibleCloseds X)
abbrev IsIrreduciblyNoetherianTopologicalSpace := IsDiscreteOrder (IrreducibleCloseds X)

noncomputable def top_open_iso_univ : (⊤ : Opens X) ≃ₜ X := IsEmbedding.toHomeomorph_of_surjective Topology.IsEmbedding.subtypeVal (by intro x; use ⟨x, trivial⟩)

lemma isCatenary_of_iso_isCatenary {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Y_catenary : IsCatenaryTopologicalSpace Y) (φ : X ≃ₜ Y) : IsCatenaryTopologicalSpace X := ⟨by intro T T'; obtain ⟨n, h⟩ := Y_catenary.isCatenary ⟨(φ '' T), sorry, sorry⟩ ⟨(φ '' T'), sorry, sorry⟩; use n; intro x; sorry⟩

-- lemma 5.11.5 part 1
lemma catenary_iff_catenary_cover : IsCatenaryTopologicalSpace X ↔ ∃ ι : Type, ∃ u : ι → Opens X, IsOpenCover u ∧ ∀ i : ι, IsCatenaryTopologicalSpace (u i) := by
  constructor
  · intro h
    use Finset.range 1, fun i ↦ ⊤
    constructor
    · simp only [IsOpenCover, Finset.range_one, ciSup_unique]
    · simp only [Finset.range_one, Finset.mem_singleton, forall_const]
      exact isCatenary_of_iso_isCatenary h (top_open_iso_univ X)
  · intro exists_cat_cov
    constructor
    intro T T'
    by_cases h : T = T'
    · simp
      use 0
      intro x
      -- rw [← h] at x
      use x, (by rfl)
      match x with
      | RelSeriesHT.singleton T => rfl
      | RelSeriesHT.cons T l Tltb => simp; have : T < T' := sorry; rw [h] at this; exact lt_irrefl T' this --lt_trans Tltb (lt_of_relSeriesHT)
      -- have : x = singleton T := by
      --   match x with
      --   | RelSeriesHT.singleton T => rfl
      --   | RelSeriesHT.cons T l Tltb => rw [← h] at x; sorry--have : T < T := lt_of_relSeriesHT
      -- nth_rw 2 [h] at x -- why do I constantly have to rewrite x?
      -- use x
      -- constructor
      -- · constructor
      --   intro y xley

      -- have : T < T' := lt_of_relSeriesHT x

    · push_neg at h
      by_cases TltT' : ¬ T < T'
      · use 0
        intro x
        have : T < T' := lt_of_relSeriesHT h x
        contradiction
      push_neg at TltT'
      obtain ⟨ι, u, u_cov, ui_cat⟩ := exists_cat_cov
      have : ∃ i, ((u i : Set X) ∩ T).Nonempty := by
        obtain ⟨t, t_mem_T⟩ := T.is_irreducible'.1
        obtain ⟨i, t_mem_ui⟩ := IsOpenCover.exists_mem u_cov t
        use i, t
        constructor <;> assumption
      obtain ⟨i, ui_inter⟩ := this
      obtain ⟨n, h⟩ := (ui_cat i).isCatenary ((closure_irred (u i).is_open').invFun ⟨T, by obtain ⟨x, x_mem⟩ := ui_inter; simp at x_mem; use ⟨x, x_mem.left⟩; simp; exact x_mem.right⟩) ((closure_irred (u i).is_open').invFun ⟨T', by obtain ⟨x, x_mem⟩ := ui_inter; simp at x_mem; use ⟨x, x_mem.left⟩; simp; exact mem_of_mem_of_subset x_mem.right (by simp; exact TltT'.left)⟩) -- can use properties of closure_irred for this?
      use n
      intro x
      have ui_: ((u i : Set X) ∩ T).Nonempty := by obtain ⟨x, x_mem⟩ := ui_inter; use x
      have : T = closure_irred (u i).is_open' ((closure_irred (u i).is_open').invFun ⟨T, by obtain ⟨x, x_mem⟩ := ui_inter; simp at x_mem; use ⟨x, x_mem.left⟩; simp; exact x_mem.right⟩) := by
        simp [(closure_irred (u i).is_open').right_inv' ⟨T, by obtain ⟨x, x_mem⟩ := ui_inter; simp at x_mem; use ⟨x, x_mem.left⟩; simp; exact x_mem.right⟩]
        sorry
      simp [closure_irred] at h
      obtain ⟨y, h⟩ := h x

-- lemma 5.11.5 part 2
lemma locally_closed_subspace_catenary_of_catenary : IsCatenaryTopologicalSpace X → ∀ Y : Set X, IsLocallyClosed Y → IsCatenaryTopologicalSpace Y := sorry

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
