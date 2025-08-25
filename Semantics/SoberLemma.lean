import Mathlib.Topology.Sober
import Mathlib.Topology.Order.Category.FrameAdjunction
import Mathlib.Topology.Category.Locale
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Specialization
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.Basic
import Lean.Parser.Tactic
import Mathlib.Topology.Sets.Opens

import Semantics.Defs
import Semantics.TopologicalBasis

-- TODO consider namespaces and sections
set_option autoImplicit false
open Locale TopCat CategoryTheory TopologicalSpace Topology.IsScott

def Sober (X : TopCat) := IsHomeomorph (adjunctionTopToLocalePT.unit.app X)

--  TODO prove equivalnce of alternative defenitions of Sober
-- def Sober (X : TopCat): Prop := QuasiSober X ∧ T0Space X
--  could use a TFAE block
-- lemma alt_def {X: TopCat} : QuasiSober X ∧ T0Space X
--    ↔ Sober X := by sorry

variable {D : Type*} [AlgebraicDCPO D]

/-- Scott Topology on AlgebraicDCPO D -/
instance : TopologicalSpace D := Topology.scott D {d | DirectedOn (· ≤ ·) d}

/-- We claim that x is entirely determined by its set of basic opens `K x`.
    Proving this correspondence establishes the homeomorphism below. -/
abbrev K (x: PT (Opens D)) := { c | ∃ hc: c ∈ 𝕂 D, x <| ⟨c, hc⟩ᵘᵒ }

/-- Could add this to Mathlib. Lean's automation can prove this easily enough if a simp [map_sSup, sSup_Prop_eq].
    But I think using this lemma improves readability -/
lemma of_completelyPrime  {P: Opens D → Prop} {x: PT (Opens D)} : (x (sSup {u | P u})) ↔ ∃ u, P u ∧ x u := by
  simp only [map_sSup, sSup_Prop_eq]
  constructor
  · rintro ⟨h, ⟨h2, h3, h4⟩, h5⟩
    use h2
    subst h4
    exact ⟨h3, h5⟩
  · rintro ⟨u, hu, hxu⟩
    use x u
    simp only [Set.mem_image, Set.mem_setOf_eq, eq_iff_iff]
    constructor
    · use u
    · exact hxu

lemma directed_Kₓ (x: PT (Opens D)) : DirectedOn (· ≤ ·) (K x) := by
  rintro c ⟨hc₀, hc₁⟩ d ⟨hd₀, hd₁⟩
  let inf := ⟨c, hc₀⟩ᵘᵒ  ⊓ ⟨d, hd₀⟩ᵘᵒ
  have inf_in_x : x inf := by
    simp only [map_inf, inf]
    exact ⟨hc₁, hd₁⟩

  have this := by
    rw [open_eq_open_of_basis' inf] at inf_in_x
    exact of_completelyPrime.1 inf_in_x

  obtain ⟨e', ⟨e, he₀, he'₀, he'₁⟩, he'₂⟩ := this

  rw [he'₁] at he'₂
  use e
  constructor
  · simp only [Set.mem_setOf_eq, inf]
    exact ⟨he₀, he'₂⟩
  · simp only [inf]
    simp [inf, open_of_compact] at he'₀
    obtain ⟨h₁, h₂⟩ := he'₀
    exact ⟨h₁, h₂⟩

-- TODO maybe this lemma is already in mathlib if i use `Ici`, Mathlib's version of upperSet
lemma le_iff_ge_upperSet {α: Type*} (c e : α) [Preorder α] : c ≤ e ↔ eᵘ ⊆ cᵘ := by
  simp [upperSet]
  constructor
  · intro hec x hxc
    exact Preorder.le_trans c e x hec hxc
  · intro x
    apply x e
    rfl

lemma surjectivity: Function.Surjective (localePointOfSpacePoint D) := by
      intro x
      dsimp [pt, PT] at x
      let Kₓ := K x
      let inp := sSup Kₓ
      use inp
      apply FrameHom.ext
      intro u
      simp only [eq_iff_iff]
      change sSup Kₓ ∈ u ↔ x u

      calc
        _ ↔ sSup Kₓ ∈ u.carrier := by rfl
        _ ↔ sSup Kₓ ∈ ⋃₀ (upperSet '' { e ∈ 𝕂 D | eᵘ ⊆ u}) := by
          nth_rewrite 1 [open_eq_open_of_basis u.carrier u.isOpen]
          rfl
        _ ↔ ∃ e ∈ 𝕂 D, eᵘ ⊆ u ∧ e ≤ sSup Kₓ := by
          constructor
          · rintro ⟨e', he'₀, he'₁⟩
            simp only [Set.mem_image, Set.mem_setOf_eq] at he'₀
            choose e he₁ he₂ using he'₀
            use e
            simp only [← he₂, upperSet, Set.mem_setOf_eq] at he'₁
            exact ⟨he₁.1, he₁.2, he'₁⟩
          · rintro ⟨e, he₀, he₁, he₂⟩
            have he'₀ : eᵘ ∈ (upperSet '' {c | c ∈ 𝕂 D ∧ cᵘ ⊆ u}) := by
              simp only [Set.mem_image, Set.mem_setOf_eq]
              use e
            apply Set.subset_sUnion_of_mem at he'₀
            have he₂ : sSup Kₓ ∈ eᵘ := by aesop
            exact Set.mem_of_mem_of_subset he₂ he'₀
        _ ↔ ∃ (e c : D), c ∈ Kₓ ∧ e ∈ 𝕂 D  ∧ eᵘ ⊆ u ∧ e ≤ c := by
            constructor
            · rintro ⟨e, he₀, he'₀, he₁⟩
              use e
              choose c hc₁ hc₂ using he₀ Kₓ (directed_Kₓ x) he₁
              use c
            · rintro ⟨e, c, hc₀, he₀, he'₀, e_le_c⟩
              use e
              have he₁ : e ≤ sSup Kₓ := by
                trans c
                · assumption
                · have sSup_is_LUB := CompletePartialOrder.lubOfDirected Kₓ (directed_Kₓ x)
                  exact sSup_is_LUB.1 hc₀
              exact ⟨he₀, he'₀, he₁⟩
        _ ↔ ∃ (e c : D) (hc: c ∈ 𝕂 D), e ∈ 𝕂 D ∧ eᵘ ⊆ u ∧ cᵘ ⊆ eᵘ ∧ x (⟨c, hc⟩ᵘᵒ) := by
          constructor
          · rintro ⟨e, c, ⟨hc₀, hc₁⟩, he₀, he₁, e_le_c⟩
            use e; use c; use hc₀
            exact ⟨he₀, he₁, by rwa [← le_iff_ge_upperSet e c], hc₁⟩

          · rintro ⟨e, c, hc₀, he₀, he'₀, c'_le_e', hc'₀⟩
            use e; use c;
            exact ⟨⟨hc₀, hc'₀⟩, he₀, he'₀, by rwa [le_iff_ge_upperSet e c]⟩
        _ ↔ ∃ (e: D) (he: e ∈ 𝕂 D), eᵘ ⊆ u ∧ x (⟨e, he⟩ᵘᵒ) := by
          constructor
          · rintro ⟨e, c, hc₀, he₀, he'₀, c'_le_e', hc'₀⟩
            use e; use he₀; use he'₀
            have foo : ⟨c, hc₀⟩ᵘᵒ ⊓ ⟨e, he₀⟩ᵘᵒ = ⟨c, hc₀⟩ᵘᵒ := by simpa [open_of_compact]
            have bar : x (⟨c, hc₀⟩ᵘᵒ ⊓ ⟨e, he₀⟩ᵘᵒ) = x (⟨c, hc₀⟩ᵘᵒ) := by simp_all
            simp [map_sSup] at bar
            exact bar hc'₀
          · -- the reverse direction is a bit silly as the requirements for c are all satisfied by e itself
            intro ⟨e, he₀, he'₀, he'₁⟩
            use e; use e; use he₀;
        _ ↔ x u := by
          constructor
          · let P (o: Opens D) := ∃ (c: D) (hc: c ∈ 𝕂 D), c ∈ u ∧ (o = ⟨c, hc⟩ᵘᵒ)
            -- intro he
            rintro ⟨e, he₀, he'₀, he'₁⟩
            have he': ∃ u, P u ∧ x u := by
              use ⟨e, he₀⟩ᵘᵒ
              exact ⟨⟨e, he₀, mem_iff_upSet_subset.2 he'₀, rfl⟩, he'₁⟩

            rw [← of_completelyPrime] at he'
            rw [← open_eq_open_of_basis' u] at he'
            exact he'
          · intro hu
            rw [open_eq_open_of_basis' u] at hu
            rw [of_completelyPrime] at hu

            obtain ⟨e', ⟨e, he₀, he'₀, he'₁⟩ , he'₂⟩ := hu
            rw [he'₁] at he'₂
            exact ⟨e, he₀, mem_iff_upSet_subset.1 he'₀, he'₂⟩

theorem scottIsSober : Sober (@TopCat.of D (Topology.scott D {d | DirectedOn (· ≤ ·) d})) := by
  dsimp only [Functor.id_obj, Functor.comp_obj, topToLocale_obj, adjunctionTopToLocalePT,
        topCatOpToFrm_obj_coe, hom_ofHom, Sober]
  constructor
  · continuity
  · -- Open Map
    intro u hu
    use ⟨u, hu⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.image]
    dsimp only [topCatOpToFrm_obj_coe] at x
    constructor
    · intro he
      choose e he' using (surjectivity x)
      subst he'
      exact ⟨e, he, by rfl⟩
    · intro hx
      choose e he he' using hx
      subst he'
      exact he
  · -- Bijective
    constructor
    · -- Injective
      intro d e
      contrapose
      intro d_ne_e

      change ¬ ((localePointOfSpacePoint D d) = (localePointOfSpacePoint D e))
      rw [@FrameHom.ext_iff (Opens D) Prop (Opens.instCompleteLattice) Prop.instCompleteLattice (localePointOfSpacePoint D d) (localePointOfSpacePoint D e)]
      simp only [localePointOfSpacePoint_toFun, eq_iff_iff, not_forall]
      rcases (@Ne.not_le_or_not_le D _ _ _ d_ne_e) with d_nle_e | e_nle_d
      ·
        simp only [specialization_iff_ge, specializes_iff_forall_open, not_forall,
          Classical.not_imp] at d_nle_e
        obtain ⟨u, hu, d_in_u, e_ne_u⟩ := d_nle_e
        use ⟨u, hu⟩
        simp only [Opens.mem_mk]
        intro h
        exact (and_not_self_iff (e ∈ u)).1 ⟨h.1 d_in_u, e_ne_u⟩
      · -- This follows dually from above. Attempting to resuse the above proof was unseccessfule
        -- CompletePartialOrder instance for the dual type not implemented.
        -- To do so binary relation, `r` of DirectedOn needs to be inverted, but `r` is not stored/accessible.
        -- It would be if DierctedOn was a struct rather than a function
        simp only [specialization_iff_ge, specializes_iff_forall_open, not_forall,
          Classical.not_imp] at e_nle_d
        obtain ⟨u, hu, e_in_u, d_ne_u⟩ := e_nle_d
        use ⟨u, hu⟩
        simp only [Opens.mem_mk]
        intro h
        exact (and_not_self_iff (d ∈ u)).1 ⟨h.2 e_in_u, d_ne_u⟩
    · -- Surjective
      exact surjectivity
