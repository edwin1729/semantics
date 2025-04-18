lemma compactFromElement {α : Type*} [AlgebraicDCPO α] {x : α} (u : Set α) (x_in_u: x ∈ u) (hu : IsOpen u)  :
  ∃ c ∈ 𝕂 α, x ∈ upperSet c ∧ upperSet c ⊆ u := by

    rw [@isOpen_iff_isUpperSet_and_dirSupInaccOn α {d | DirectedOn (· ≤ ·) d }, DirSupInaccOn] at hu

    obtain ⟨upper, hausdorff⟩ := hu
    have compactLowerBounded : ∀ x ∈ u, ∃ c: α, c ≤ x ∧ c ∈ u ∧ compact c := by
      intro x x_in_u
      -- the Algebraicity property
      obtain ⟨nonempty, directedCls, join⟩ := AlgebraicDCPO.algebraic x
      -- simp only [Function.comp_apply] at hausdorff

      -- We work with this cls to extract an elememt from it satisfying our needs
      let cls := (compactLowerSet x)

      -- by algebraicity, an element, `x`, is the meet of its `cls`
      have x_is_LUB : IsLUB cls x:= by
        rw [join]
        apply CompletePartialOrder.lubOfDirected cls directedCls

      -- We use the innacessible joins property to show get a nonempty intersection
      -- The intersection contains exactly what we want, a compact element in u and ≤ x
      have nonempty_inter := hausdorff directedCls nonempty directedCls x_is_LUB x_in_u
      simp only [compactLowerSet, inter_nonempty, mem_inter_iff, mem_setOf_eq] at nonempty_inter

      -- This is the funny bit where I decided it's cleanest to extract boilerplate to `aesopify`
      change ∃ c, (c ≤ x ∧ compact c) ∧ c ∈ u at nonempty_inter
      have : ∃ c ≤ x, c ∈ u ∧ compact c:= aesopify nonempty_inter
      exact this
    -- given an x ∈ u, take it to its compact element
    choose f hf hf' hf'' using compactLowerBounded
    let f' : {x : α // x ∈ u} → α := λ x => f x.1 x.2
    use f' ⟨x, x_in_u⟩
    --  ∃ v ∈ _root_.upperSet '' 𝕂 α, x ∈ v ∧ v ⊆ u

    constructor
    · apply hf''
    · constructor
      · apply hf
      · intro y hy
        aesop


--  (U : Set α) (h: IsOpen U) :
lemma constructOpenFromCompact {α : Type*} [AlgebraicDCPO α] (u : Set α) {hu : IsOpen u} :
  u ⊆ ⋃₀ { upperSet c | c ∈ u ∩ 𝕂 α} := by
    intro x x_in_u
    simp only [mem_inter_iff, mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and]
    obtain ⟨a,b,c,d⟩ := compactFromElement u x_in_u hu
    -- use x
    sorry
