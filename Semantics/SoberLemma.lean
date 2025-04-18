import Mathlib.Topology.Sober
import Mathlib.Topology.Order.Category.FrameAdjunction
import Mathlib.Topology.Category.Locale
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Specialization
import Mathlib.Topology.Order.ScottTopology
import Lean.Parser.Tactic
import Mathlib.Topology.Sets.Opens

import Semantics.Defs

set_option autoImplicit false
open Locale TopCat CategoryTheory TopologicalSpace

def Sober (X : TopCat): Prop := QuasiSober X ∧ T0Space X

/-- Alternative definitions of Sober. Equivalence assumed -/
def adjunctionHomeomorphism {X: TopCat} : IsHomeomorph (adjunctionTopToLocalePT.unit.app X)
    ↔ Sober X := by sorry

/-- Redefining filters here since our filters may also be empty
So Set.univ need not be included-/
structure CompletelyPrimeFilter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets
  /-- CompletelyPrime -/
  prime {S : Set (Set α)} : ⋃₀ S ∈ sets → ∃ s ∈ S, s ∈ sets

-- Stuggled to find the lemma or define myself the lemma that FrameHom is monotonic over the specialization order
-- This is a lemma certainly be already in Mathlib in a different form
-- lemma monotonicity {α : Type*} {β : Type*} [CompleteLattice α] [LE α] [CompleteLattice β] (FrameHom α β) (x y: α) : Specialization.ofEquiv x ≤ Specialization.ofEquiv y → FrameHom α β x ≤ FrameHom α β y := by
  -- sorry

variable {D : Type*} [AlgebraicDCPO D]

/-- Scott Topology on AlgebraicDCPO D -/
instance : TopologicalSpace D := Topology.scott D {d | DirectedOn (· ≤ ·) d}

-- attempted to prove this more general result but I couldn't make progress even though it was
-- conceptually simple because of "Sort Mixing" problem, ie usage of `Prop` in `PT`

-- def alternative_pt {α: Type*} [CompleteLattice α] : PT (Set α) ≃ CompletelyPrimeFilter α where

/-- Defines one side of the equivalence between to two alternative definitions of completely prime filters
I struggled to prove this since I can't quite get the lattice structure on Prop to behave -/
def mkPrimeFilter {α: Type*} [AlgebraicDCPO α] (f: PT (Set α)): CompletelyPrimeFilter α := {
      sets := {u | f u}
      , sets_of_superset := by
        intros x y hx hxy
        simp only [Set.mem_setOf_eq] at hx
        simp only [Set.mem_setOf_eq]
        -- #check (map_lt_map_iff f) -- doesn't work
        -- I would want to do something like this if FrameHom had an instance of EquivLike
        -- apply map_lt_map_iff f hxy
        -- It makes sense that it doesn't, but I don't see anything called HomLike
        -- or any direct lemmas that provide a specialization order
        -- using the monotonicity lemma we can say that f x ≤ f y
        -- But f x is ⊤, and only ⊤ ≥ ⊤, so f y holds, ie it is in the filter
        sorry

      , inter_sets := by
        intros x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy
        simp only [Set.mem_setOf_eq]
        have hmap_inf : f (x ⊓ y) = f x ⊓ f y:= (map_inf f x y)
        -- have inf := hx ∧ hy -- why doesn't this work? It's supposed to be the meet of 2 Props
        sorry

      , prime := by
        intro S hS
        simp only [Set.mem_setOf_eq] at hS
        sorry

}

/-- The set we work with throughout the surjectivity proof -/
abbrev K (x: Set (Set D)):= {c ∈ 𝕂 D | (upperSet c) ∈ x}

/-- Results from previous project.
They just need to be extracted as they are intermediate not final results-/
lemma constructOpenFromCompact' (u : Set D) (hu : IsOpen u) :
  u = ⋃₀ { upperSet c | c ∈ u ∩ 𝕂 D} := sorry

/-- Results from previous project.
They just need to be extracted as they are intermediate not final results-/
lemma constructOpenFromCompact (u : Set D) (hu : IsOpen u) :
  u = ⋃₀ (upperSet '' { c ∈ 𝕂 D | cᵘ ⊆ u}) := sorry

/-- The calc proof required to show surjectivity -/
lemma surjectivity {u: Set D} (hu: IsOpen u) (x: CompletelyPrimeFilter D)
  : sSup (K x.sets) ∈ u ↔ u ∈ x.sets  :=
  let Kₓ := K x.sets
  calc
    sSup (K x.sets) ∈ u ↔ sSup Kₓ ∈ ⋃₀ (upperSet '' { c ∈ 𝕂 D | cᵘ ⊆ u}) := by
      nth_rewrite 1 [constructOpenFromCompact u hu]
      rfl
    -- _ ↔ ∃ e ∈ 𝕂 D, eᵘ ⊆ u ∧ sSup Kₓ ∈ eᵘ :=
    _ ↔ ∃ e ∈ 𝕂 D, eᵘ ⊆ u ∧ e ≤ sSup Kₓ := by
      constructor
      · -- →
        rintro ⟨e', he'₀, he'₁⟩
        simp only [Set.mem_image, Set.mem_setOf_eq] at he'₀
        choose e he₁ he₂ using he'₀
        use e
        simp only [← he₂, upperSet, Set.mem_setOf_eq] at he'₁
        exact ⟨he₁.1, he₁.2, he'₁⟩
      · -- ←
        rintro ⟨e, he₀, he₁, he₂⟩
        have he'₀ : eᵘ ∈ (upperSet '' {c | c ∈ 𝕂 D ∧ cᵘ ⊆ u}) := by
          simp only [Set.mem_image, Set.mem_setOf_eq]
          use e
        apply Set.subset_sUnion_of_mem at he'₀
        have he₂ : sSup Kₓ ∈ eᵘ := by aesop
        exact Set.mem_of_mem_of_subset he₂ he'₀
    -- _ ↔ ∃ e ∈ 𝕂 D, ∃ c ∈ Kₓ, eᵘ ⊆ u ∧ e ≤ c :=
    _ ↔ ∃ e ∈ 𝕂 D, ∃ c ∈ 𝕂 D, eᵘ ⊆ u ∧ cᵘ ⊆ eᵘ ∧ cᵘ ∈ x.sets := by
      constructor
      · -- →
        rintro ⟨e, he₀, he'₀, he₁⟩
        use e
        sorry
      · -- ←
        rintro ⟨e, he₀, c, hc₀, he₁, hc₁⟩
        use e
        sorry
    _ ↔ ∃ e ∈ 𝕂 D, eᵘ ⊆ u ∧ eᵘ ∈ x.sets := sorry
    _ ↔ u ∈ x.sets := sorry


theorem scottIsSober : Sober (@TopCat.of D (Topology.scott D {d | DirectedOn (· ≤ ·) d})) := by
  apply adjunctionHomeomorphism.1
  -- #check (adjunctionTopToLocalePT.unit.app X)
  -- have : X ≃ₜ ((topToLocale ⋙ pt).obj X) := sorry
  constructor
  · -- continuity obtained since we have a morphism in the category of topological spaces
    -- should have been quite easy to prove...
    sorry
  · -- Open Map
    sorry
  · -- Bijective
    constructor
    · -- Injective
      -- change Function.Injective (λ _ → _)--(λ (d: X) → {U | IsOpen U ∧ d ∈ U}))
      #check ⇑(ConcreteCategory.hom (adjunctionTopToLocalePT.unit.app (TopCat.of D)))
      change Function.Injective ⇑(ConcreteCategory.hom (adjunctionTopToLocalePT.unit.app (TopCat.of D)))
      have t0 : T0Space Y := sorry

      intro d e hde
      let d' := (ConcreteCategory.hom (adjunctionTopToLocalePT.unit.app (TopCat.of D))) d
      let e' := (ConcreteCategory.hom (adjunctionTopToLocalePT.unit.app (TopCat.of D))) e
      have foo := Specialization (↑(TopCat.of D))
      -- apply le_antisymm_iff at hde
      sorry
    · -- Surjective
      intro x
      simp only [Functor.comp_obj] at x
      simp [pt, PT] at x
      let openSet := Opens.carrier '' { y | x y}
      have openSetIsOpen : ∀ u ∈ openSet, IsOpen u := by
        intro u hu
        rw [Set.mem_image] at hu
        sorry

      -- This will be a frame homomorphism it's just a forgetful one should be trivial to construct
      have homOS : FrameHom (Set D) (Opens D) := sorry
      let x' : CompletelyPrimeFilter D := mkPrimeFilter (x.comp homOS)
      dsimp only [Functor.id_obj, Functor.comp_obj, topToLocale_obj, adjunctionTopToLocalePT,
        topCatOpToFrm_obj_coe, hom_ofHom]
      -- simp only [Functor.id_obj, Functor.comp_obj, topToLocale_obj]

      -- The join of `Kₓ` is to be shown as the input mapping to `x`
      let Kₓ := K x'.sets
      -- We first need to show that K is directed: see InformalProof.txt
      have IsDirected : DirectedOn (· ≤ ·) Kₓ := by
        intro c hc d hd

        let c' := upperSet c
        let d' := upperSet d
        have h_inf' : c' ∩ d' ∈ x'.sets := x'.inter_sets hc.2 hd.2
        have inf_as_sup := constructOpenFromCompact' (c' ∩ d') (by apply openSetIsOpen; exact h_inter')
        have h_inf'' : ⋃₀ {x | ∃ c_1 ∈ c' ∩ d' ∩ 𝕂 D, upperSet c_1 = x} ∈ x'.sets := by
          rwa [inf_as_sup] at h_inf'
        choose e' he'₀ he'₁ using (x'.prime h_inf'')
        dsimp only [Set.mem_inter_iff, Set.mem_setOf_eq] at he'₀
        choose e he₀ hee' using he'₀
        obtain ⟨⟨e_in_c', e_in_d'⟩, he_compact⟩ := he₀
        have e_in_Kₓ : e ∈ Kₓ := by
          dsimp only [Set.mem_setOf_eq, Kₓ]
          constructor
          · -- e ∈ 𝕂 D
            exact he_compact
          · -- upperSet e ∈ x'.sets
            rw [hee']
            exact he'₁
        use e
        constructor
        · -- e ∈ Kₓ
          exact e_in_Kₓ
        constructor
        · -- e ≤ c
          dsimp only [Kₓ]
          exact e_in_c'
        · dsimp only [Kₓ]
          exact e_in_d'
      have sSup_is_LUB := CompletePartialOrder.lubOfDirected Kₓ IsDirected
      use sSup Kₓ
      let foo :=  localePointOfSpacePoint D (sSup Kₓ)
      let foo' := {u: Opens D | localePointOfSpacePoint D (sSup Kₓ) u}
      -- simp? [localePointOfSpacePoint] at foo' -- does nothing useful
      sorry

#lint
