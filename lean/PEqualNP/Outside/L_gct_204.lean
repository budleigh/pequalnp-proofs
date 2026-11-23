import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Gct204

open Finset

private def leftPart {n1 n2 : ℕ} (S : Finset (Fin (n1 + n2))) : Finset (Fin n1) :=
  Finset.univ.filter fun i => finSumFinEquiv (Sum.inl i) ∈ S

private def rightPart {n1 n2 : ℕ} (S : Finset (Fin (n1 + n2))) : Finset (Fin n2) :=
  Finset.univ.filter fun j => finSumFinEquiv (Sum.inr j) ∈ S

private def combine {n1 n2 : ℕ} (S1 : Finset (Fin n1)) (S2 : Finset (Fin n2)) :
    Finset (Fin (n1 + n2)) :=
  S1.image (fun i => finSumFinEquiv (Sum.inl i)) ∪ S2.image (fun j => finSumFinEquiv (Sum.inr j))

private lemma mem_combine_inl {n1 n2 : ℕ} (S1 : Finset (Fin n1)) (S2 : Finset (Fin n2)) (i : Fin n1) :
    finSumFinEquiv (Sum.inl i) ∈ combine S1 S2 ↔ i ∈ S1 := by
  simp only [combine, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨i', hi', h⟩ | ⟨j, _, h⟩)
    · exact Sum.inl.inj (finSumFinEquiv.injective h) ▸ hi'
    · exact False.elim (Sum.inr_ne_inl (finSumFinEquiv.injective h))
  · intro hi
    exact Or.inl ⟨i, hi, rfl⟩

private lemma mem_combine_inr {n1 n2 : ℕ} (S1 : Finset (Fin n1)) (S2 : Finset (Fin n2)) (j : Fin n2) :
    finSumFinEquiv (Sum.inr j) ∈ combine S1 S2 ↔ j ∈ S2 := by
  simp only [combine, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨i, _, h⟩ | ⟨j', hj', h⟩)
    · exact False.elim (Sum.inl_ne_inr (finSumFinEquiv.injective h))
    · exact Sum.inr.inj (finSumFinEquiv.injective h) ▸ hj'
  · intro hj
    exact Or.inr ⟨j, hj, rfl⟩

private lemma combine_left_right {n1 n2 : ℕ} (S : Finset (Fin (n1 + n2))) :
    combine (leftPart S) (rightPart S) = S := by
  ext x
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective x
  cases y with
  | inl i =>
    rw [mem_combine_inl]
    simp only [leftPart, Finset.mem_filter, Finset.mem_univ, true_and]
  | inr j =>
    rw [mem_combine_inr]
    simp only [rightPart, Finset.mem_filter, Finset.mem_univ, true_and]

private lemma leftPart_combine {n1 n2 : ℕ} (S1 : Finset (Fin n1)) (S2 : Finset (Fin n2)) :
    leftPart (combine S1 S2) = S1 := by
  ext i
  simp only [leftPart, Finset.mem_filter, Finset.mem_univ, true_and, mem_combine_inl]

private lemma rightPart_combine {n1 n2 : ℕ} (S1 : Finset (Fin n1)) (S2 : Finset (Fin n2)) :
    rightPart (combine S1 S2) = S2 := by
  ext j
  simp only [rightPart, Finset.mem_filter, Finset.mem_univ, true_and, mem_combine_inr]

private lemma card_combine {n1 n2 : ℕ} (S1 : Finset (Fin n1)) (S2 : Finset (Fin n2)) :
    (combine S1 S2).card = S1.card + S2.card := by
  have hdisj : Disjoint (S1.image (fun i => finSumFinEquiv (Sum.inl i)))
      (S2.image (fun j => finSumFinEquiv (Sum.inr j))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨j, _, h⟩ := Finset.mem_image.mp hx2
    exact Sum.inr_ne_inl (finSumFinEquiv.injective h)
  rw [combine, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj (finSumFinEquiv.injective h)),
    Finset.card_image_of_injective _ (fun _ _ h => Sum.inr.inj (finSumFinEquiv.injective h))]

private def splitFinsetEquiv (n1 n2 : ℕ) :
    Finset (Fin (n1 + n2)) ≃ Finset (Fin n1) × Finset (Fin n2) where
  toFun S := (leftPart S, rightPart S)
  invFun p := combine p.1 p.2
  left_inv S := combine_left_right S
  right_inv p := Prod.ext (leftPart_combine p.1 p.2) (rightPart_combine p.1 p.2)

private lemma orderEmbOfFin_combine {n1 n2 k1 k2 k : ℕ}
    (S1 : Finset (Fin n1)) (S2 : Finset (Fin n2))
    (h1 : S1.card = k1) (h2 : S2.card = k2) (hk : (combine S1 S2).card = k)
    (heq : k1 + k2 = k) :
    ∀ x : Fin k,
      (combine S1 S2).orderEmbOfFin hk x =
        match finSumFinEquiv.symm (Fin.cast heq.symm x) with
        | Sum.inl a => finSumFinEquiv (Sum.inl (S1.orderEmbOfFin h1 a))
        | Sum.inr b => finSumFinEquiv (Sum.inr (S2.orderEmbOfFin h2 b)) := by
  let f : Fin k → Fin (n1 + n2) := fun x =>
    match finSumFinEquiv.symm (Fin.cast heq.symm x) with
    | Sum.inl a => finSumFinEquiv (Sum.inl (S1.orderEmbOfFin h1 a))
    | Sum.inr b => finSumFinEquiv (Sum.inr (S2.orderEmbOfFin h2 b))
  have hf_strict : StrictMono f := by
    intro x y hxy
    have hxy' : (Fin.cast heq.symm x : Fin (k1 + k2)) < Fin.cast heq.symm y := hxy
    dsimp only [f]
    cases hx : finSumFinEquiv.symm (Fin.cast heq.symm x) with
    | inl ax =>
      cases hy : finSumFinEquiv.symm (Fin.cast heq.symm y) with
      | inl ay =>
        have hax : (Fin.cast heq.symm x).val = ax.val := by
          have := congrArg finSumFinEquiv hx
          rw [Equiv.apply_symm_apply] at this
          simpa [finSumFinEquiv_apply_left] using congrArg Fin.val this
        have hay : (Fin.cast heq.symm y).val = ay.val := by
          have := congrArg finSumFinEquiv hy
          rw [Equiv.apply_symm_apply] at this
          simpa [finSumFinEquiv_apply_left] using congrArg Fin.val this
        have hlt : ax < ay := by
          change ax.val < ay.val
          have : (Fin.cast heq.symm x).val < (Fin.cast heq.symm y).val := hxy'
          omega
        have hlt2 : S1.orderEmbOfFin h1 ax < S1.orderEmbOfFin h1 ay := (S1.orderEmbOfFin h1).strictMono hlt
        change (finSumFinEquiv (Sum.inl (S1.orderEmbOfFin h1 ax))).val <
               (finSumFinEquiv (Sum.inl (S1.orderEmbOfFin h1 ay))).val
        simpa [finSumFinEquiv_apply_left] using hlt2
      | inr byy =>
        change (finSumFinEquiv (Sum.inl (S1.orderEmbOfFin h1 ax))).val <
               (finSumFinEquiv (Sum.inr (S2.orderEmbOfFin h2 byy))).val
        simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]
        have := (S1.orderEmbOfFin h1 ax).isLt
        omega
    | inr bx =>
      cases hy : finSumFinEquiv.symm (Fin.cast heq.symm y) with
      | inl ay =>
        have hbx : (Fin.cast heq.symm x).val = k1 + bx.val := by
          have := congrArg finSumFinEquiv hx
          rw [Equiv.apply_symm_apply] at this
          simpa [finSumFinEquiv_apply_right] using congrArg Fin.val this
        have hay : (Fin.cast heq.symm y).val = ay.val := by
          have := congrArg finSumFinEquiv hy
          rw [Equiv.apply_symm_apply] at this
          simpa [finSumFinEquiv_apply_left] using congrArg Fin.val this
        have : (Fin.cast heq.symm x).val < (Fin.cast heq.symm y).val := hxy'
        have := ay.isLt
        omega
      | inr byy =>
        have hbx : (Fin.cast heq.symm x).val = k1 + bx.val := by
          have := congrArg finSumFinEquiv hx
          rw [Equiv.apply_symm_apply] at this
          simpa [finSumFinEquiv_apply_right] using congrArg Fin.val this
        have hby : (Fin.cast heq.symm y).val = k1 + byy.val := by
          have := congrArg finSumFinEquiv hy
          rw [Equiv.apply_symm_apply] at this
          simpa [finSumFinEquiv_apply_right] using congrArg Fin.val this
        have hlt : bx < byy := by
          change bx.val < byy.val
          have : (Fin.cast heq.symm x).val < (Fin.cast heq.symm y).val := hxy'
          omega
        have hlt2 : S2.orderEmbOfFin h2 bx < S2.orderEmbOfFin h2 byy := (S2.orderEmbOfFin h2).strictMono hlt
        change (finSumFinEquiv (Sum.inr (S2.orderEmbOfFin h2 bx))).val <
               (finSumFinEquiv (Sum.inr (S2.orderEmbOfFin h2 byy))).val
        simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
        have : (S2.orderEmbOfFin h2 bx).val < (S2.orderEmbOfFin h2 byy).val := hlt2
        omega
  let emb : Fin k ↪o Fin (n1 + n2) := OrderEmbedding.ofStrictMono f hf_strict
  have hrange : Set.range emb = (combine S1 S2 : Set (Fin (n1 + n2))) := by
    ext z
    simp only [Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨x, rfl⟩
      change f x ∈ combine S1 S2
      dsimp only [f]
      cases finSumFinEquiv.symm (Fin.cast heq.symm x) with
      | inl a => rw [mem_combine_inl]; exact (S1.orderIsoOfFin h1 a).2
      | inr b => rw [mem_combine_inr]; exact (S2.orderIsoOfFin h2 b).2
    · intro hz
      obtain ⟨w, rfl⟩ := finSumFinEquiv.surjective z
      cases w with
      | inl i =>
        rw [mem_combine_inl] at hz
        let a : Fin k1 := (S1.orderIsoOfFin h1).symm ⟨i, hz⟩
        refine ⟨Fin.cast heq (finSumFinEquiv (Sum.inl a)), ?_⟩
        change f (Fin.cast heq (finSumFinEquiv (Sum.inl a))) = finSumFinEquiv (Sum.inl i)
        dsimp only [f]
        simp only [Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply]
        have ha : S1.orderEmbOfFin h1 a = i := by
          change ((S1.orderIsoOfFin h1) ((S1.orderIsoOfFin h1).symm ⟨i, hz⟩)).1 = i
          simp
        rw [ha]
      | inr j =>
        rw [mem_combine_inr] at hz
        let b : Fin k2 := (S2.orderIsoOfFin h2).symm ⟨j, hz⟩
        refine ⟨Fin.cast heq (finSumFinEquiv (Sum.inr b)), ?_⟩
        change f (Fin.cast heq (finSumFinEquiv (Sum.inr b))) = finSumFinEquiv (Sum.inr j)
        dsimp only [f]
        simp only [Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply]
        have hb : S2.orderEmbOfFin h2 b = j := by
          change ((S2.orderIsoOfFin h2) ((S2.orderIsoOfFin h2).symm ⟨j, hz⟩)).1 = j
          simp
        rw [hb]
  have hemb : (combine S1 S2).orderEmbOfFin hk = emb := by
    have h1' : Set.range ((combine S1 S2).orderEmbOfFin hk) = Set.range emb := by
      rw [Finset.range_orderEmbOfFin, hrange]
    exact OrderEmbedding.eq_of_range_eq h1'
  intro x
  rw [hemb]
  rfl

private lemma perm_block_ne {p1 q1 p2 q2 k : ℕ}
    (t1 : Fin p1 × Fin q1 → ℂ) (t2 : Fin p2 × Fin q2 → ℂ)
    (T : Fin (p1 + p2) × Fin (q1 + q2) → ℂ)
    (hT : ∀ x, T x = Matrix.fromBlocks (Matrix.of fun a b => t1 (a, b)) 0 0
        (Matrix.of fun a b => t2 (a, b)) (finSumFinEquiv.symm x.1) (finSumFinEquiv.symm x.2))
    (R1 : Finset (Fin p1)) (R2 : Finset (Fin p2))
    (C1 : Finset (Fin q1)) (C2 : Finset (Fin q2))
    (hR : (combine R1 R2).card = k) (hC : (combine C1 C2).card = k)
    (hne : R1.card ≠ C1.card) :
    Matrix.permanent (Matrix.of fun a b =>
      T ((combine R1 R2).orderEmbOfFin hR a, (combine C1 C2).orderEmbOfFin hC b)) = 0 := by
  have hkR : R1.card + R2.card = k := by rw [← card_combine, hR]
  have hkC : C1.card + C2.card = k := by rw [← card_combine, hC]
  rw [Matrix.permanent]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have hbad : ∃ b : Fin k, (σ b).val < R1.card ↔ ¬ (b.val < C1.card) := by
    by_contra hall
    have hiff : ∀ b : Fin k, (σ b).val < R1.card ↔ b.val < C1.card := by
      intro b
      by_cases h1 : (σ b).val < R1.card <;> by_cases h2 : b.val < C1.card
      · exact ⟨fun _ => h2, fun _ => h1⟩
      · exact False.elim (hall ⟨b, by simp [h1, h2]⟩)
      · exact False.elim (hall ⟨b, by simp [h1, h2]⟩)
      · exact ⟨fun h => False.elim (h1 h), fun h => False.elim (h2 h)⟩
    let S_C : Finset (Fin k) := Finset.univ.filter (fun b : Fin k => b.val < C1.card)
    let S_R : Finset (Fin k) := Finset.univ.filter (fun a : Fin k => a.val < R1.card)
    have himg : S_C.image σ = S_R := by
      ext a
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S_C, S_R]
      constructor
      · rintro ⟨b, hb, rfl⟩; exact (hiff b).mpr hb
      · intro ha; refine ⟨σ.symm a, ?_, Equiv.apply_symm_apply σ a⟩
        exact (hiff (σ.symm a)).mp (by simpa using ha)
    have hcard_C : S_C.card = C1.card := by
      let fC : Fin C1.card → Fin k := fun j => ⟨j.val, by omega⟩
      have hfC : Function.Injective fC := fun x y h => Fin.ext (congrArg (fun z : Fin k => z.val) h)
      have hSC : S_C = Finset.univ.image fC := by
        ext b
        simp only [S_C, fC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hb; exact ⟨⟨b.val, hb⟩, Fin.ext rfl⟩
        · rintro ⟨j, rfl⟩; exact j.isLt
      rw [hSC, Finset.card_image_of_injective _ hfC, Finset.card_univ, Fintype.card_fin]
    have hcard_R : S_R.card = R1.card := by
      let fR : Fin R1.card → Fin k := fun i => ⟨i.val, by omega⟩
      have hfR : Function.Injective fR := fun x y h => Fin.ext (congrArg (fun z : Fin k => z.val) h)
      have hSR : S_R = Finset.univ.image fR := by
        ext a
        simp only [S_R, fR, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro ha; exact ⟨⟨a.val, ha⟩, Fin.ext rfl⟩
        · rintro ⟨i, rfl⟩; exact i.isLt
      rw [hSR, Finset.card_image_of_injective _ hfR, Finset.card_univ, Fintype.card_fin]
    have hce := Finset.card_image_of_injective S_C σ.injective
    rw [himg, hcard_R, hcard_C] at hce
    exact hne hce
  obtain ⟨b, hb⟩ := hbad
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  simp only [Matrix.of_apply, hT]
  rw [orderEmbOfFin_combine R1 R2 rfl rfl hR hkR (σ b),
      orderEmbOfFin_combine C1 C2 rfl rfl hC hkC b]
  cases ha : finSumFinEquiv.symm (Fin.cast hkR.symm (σ b)) with
  | inl a1 =>
    have hlt1 : (σ b).val < R1.card := by
      have := congrArg finSumFinEquiv ha
      rw [Equiv.apply_symm_apply] at this
      have hv := congrArg Fin.val this
      simp only [Fin.val_cast, finSumFinEquiv_apply_left, Fin.val_castAdd] at hv
      rw [hv]; exact a1.isLt
    have hge2 : ¬ (b.val < C1.card) := hb.mp hlt1
    cases hc : finSumFinEquiv.symm (Fin.cast hkC.symm b) with
    | inl c1 =>
      have := congrArg finSumFinEquiv hc
      rw [Equiv.apply_symm_apply] at this
      have hv := congrArg Fin.val this
      simp only [Fin.val_cast, finSumFinEquiv_apply_left, Fin.val_castAdd] at hv
      exact False.elim (hge2 (hv ▸ c1.isLt))
    | inr c2 =>
      simp only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  | inr a2 =>
    have hge1 : ¬ ((σ b).val < R1.card) := by
      have := congrArg finSumFinEquiv ha
      rw [Equiv.apply_symm_apply] at this
      have hv := congrArg Fin.val this
      simp only [Fin.val_cast, finSumFinEquiv_apply_right, Fin.val_natAdd] at hv
      omega
    have hlt2 : b.val < C1.card := by by_contra hn; exact hge1 (hb.mpr hn)
    cases hc : finSumFinEquiv.symm (Fin.cast hkC.symm b) with
    | inl c1 =>
      simp only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    | inr c2 =>
      have := congrArg finSumFinEquiv hc
      rw [Equiv.apply_symm_apply] at this
      have hv := congrArg Fin.val this
      simp only [Fin.val_cast, finSumFinEquiv_apply_right, Fin.val_natAdd] at hv
      omega

private lemma perm_block_eq {p1 q1 p2 q2 k1 k2 k : ℕ}
    (t1 : Fin p1 × Fin q1 → ℂ) (t2 : Fin p2 × Fin q2 → ℂ)
    (T : Fin (p1 + p2) × Fin (q1 + q2) → ℂ)
    (hT : ∀ x, T x = Matrix.fromBlocks (Matrix.of fun a b => t1 (a, b)) 0 0
        (Matrix.of fun a b => t2 (a, b)) (finSumFinEquiv.symm x.1) (finSumFinEquiv.symm x.2))
    (R1 : Finset (Fin p1)) (R2 : Finset (Fin p2))
    (C1 : Finset (Fin q1)) (C2 : Finset (Fin q2))
    (hR1 : R1.card = k1) (hR2 : R2.card = k2)
    (hC1 : C1.card = k1) (hC2 : C2.card = k2)
    (hR : (combine R1 R2).card = k) (hC : (combine C1 C2).card = k)
    (hk : k1 + k2 = k) :
    Matrix.permanent (Matrix.of fun a b =>
      T ((combine R1 R2).orderEmbOfFin hR a, (combine C1 C2).orderEmbOfFin hC b)) =
    Matrix.permanent (Matrix.of fun a b => t1 (R1.orderEmbOfFin hR1 a, C1.orderEmbOfFin hC1 b)) *
    Matrix.permanent (Matrix.of fun a b => t2 (R2.orderEmbOfFin hR2 a, C2.orderEmbOfFin hC2 b)) := by
  let e : Fin k1 ⊕ Fin k2 ≃ Fin k := finSumFinEquiv.trans (finCongr hk)
  have he_inl : ∀ a : Fin k1, finSumFinEquiv.symm (Fin.cast hk.symm (e (Sum.inl a))) = Sum.inl a := by
    intro a; simp [e]
  have he_inr : ∀ b : Fin k2, finSumFinEquiv.symm (Fin.cast hk.symm (e (Sum.inr b))) = Sum.inr b := by
    intro b; simp [e]
  let M : Fin k → Fin k → ℂ := fun a b =>
    T ((combine R1 R2).orderEmbOfFin hR a, (combine C1 C2).orderEmbOfFin hC b)
  have hM_inl_inl : ∀ (a b : Fin k1),
      M (e (Sum.inl a)) (e (Sum.inl b)) = t1 (R1.orderEmbOfFin hR1 a, C1.orderEmbOfFin hC1 b) := by
    intro a b
    dsimp only [M]
    rw [hT, orderEmbOfFin_combine R1 R2 hR1 hR2 hR hk (e (Sum.inl a)),
        orderEmbOfFin_combine C1 C2 hC1 hC2 hC hk (e (Sum.inl b)), he_inl a, he_inl b]
    simp only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
  have hM_inr_inr : ∀ (a b : Fin k2),
      M (e (Sum.inr a)) (e (Sum.inr b)) = t2 (R2.orderEmbOfFin hR2 a, C2.orderEmbOfFin hC2 b) := by
    intro a b
    dsimp only [M]
    rw [hT, orderEmbOfFin_combine R1 R2 hR1 hR2 hR hk (e (Sum.inr a)),
        orderEmbOfFin_combine C1 C2 hC1 hC2 hC hk (e (Sum.inr b)), he_inr a, he_inr b]
    simp only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
  have hM_inr_inl : ∀ (a : Fin k2) (b : Fin k1), M (e (Sum.inr a)) (e (Sum.inl b)) = 0 := by
    intro a b
    dsimp only [M]
    rw [hT, orderEmbOfFin_combine R1 R2 hR1 hR2 hR hk (e (Sum.inr a)),
        orderEmbOfFin_combine C1 C2 hC1 hC2 hC hk (e (Sum.inl b)), he_inr a, he_inl b]
    simp only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  let good : Finset (Equiv.Perm (Fin k)) :=
    Finset.univ.filter fun σ => ∀ b : Fin k1, ∃ a : Fin k1, e.symm (σ (e (Sum.inl b))) = Sum.inl a
  rw [Matrix.permanent]
  have hfilt : (∑ σ : Equiv.Perm (Fin k), ∏ b : Fin k, M (σ b) b) =
      ∑ σ ∈ good, ∏ b : Fin k, M (σ b) b := by
    symm
    refine Finset.sum_subset (Finset.subset_univ good) fun σ _ hnot => ?_
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_exists] at hnot
    obtain ⟨b, hb⟩ := hnot
    refine Finset.prod_eq_zero (Finset.mem_univ (e (Sum.inl b))) ?_
    cases hval : e.symm (σ (e (Sum.inl b))) with
    | inl a => exact False.elim (hb a hval)
    | inr a =>
      have heq : σ (e (Sum.inl b)) = e (Sum.inr a) := by
        have := congrArg e hval; simpa using this
      rw [heq, hM_inr_inl]
  simp only [Matrix.of_apply]
  change (∑ σ : Equiv.Perm (Fin k), ∏ b : Fin k, M (σ b) b) = _
  rw [hfilt]
  let Φ : Equiv.Perm (Fin k1) × Equiv.Perm (Fin k2) → Equiv.Perm (Fin k) :=
    fun p => e.symm.trans ((Equiv.sumCongr p.1 p.2).trans e)
  have hsum : (∑ σ ∈ good, ∏ b : Fin k, M (σ b) b) =
      ∑ p : Equiv.Perm (Fin k1) × Equiv.Perm (Fin k2),
        (∏ b : Fin k1, t1 (R1.orderEmbOfFin hR1 (p.1 b), C1.orderEmbOfFin hC1 b)) *
        (∏ b : Fin k2, t2 (R2.orderEmbOfFin hR2 (p.2 b), C2.orderEmbOfFin hC2 b)) := by
    symm
    refine Finset.sum_nbij Φ ?_ ?_ ?_ ?_
    · rintro ⟨τ₁, τ₂⟩ _
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
      intro b
      refine ⟨τ₁ b, ?_⟩
      change e.symm (e (Equiv.sumCongr τ₁ τ₂ (e.symm (e (Sum.inl b))))) = Sum.inl (τ₁ b)
      simp
    · rintro ⟨τ₁, τ₂⟩ _ ⟨σ₁, σ₂⟩ _ heq
      have hsc : Equiv.sumCongr τ₁ τ₂ = Equiv.sumCongr σ₁ σ₂ := by
        apply Equiv.ext; intro s
        have h1 := congrArg (fun f => e.symm (f (e s))) heq
        simpa [Φ] using h1
      refine Prod.ext (Equiv.ext fun a => ?_) (Equiv.ext fun b => ?_)
      · have := congrArg (fun f => f (Sum.inl a)) hsc; simpa using this
      · have := congrArg (fun f => f (Sum.inr b)) hsc; simpa using this
    · intro σ hσ
      simp only [good, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      let ψ : Equiv.Perm (Fin k1 ⊕ Fin k2) := e.trans (σ.trans e.symm)
      have hψ_inl : ∀ b : Fin k1, ∃ a : Fin k1, ψ (Sum.inl b) = Sum.inl a := hσ
      have hψ_inr : ∀ b : Fin k2, ∃ a : Fin k2, ψ (Sum.inr b) = Sum.inr a := by
        intro b
        cases hval : ψ (Sum.inr b) with
        | inl a =>
          -- Every Sum.inl a is hit by some Sum.inl b' since Fin k1 is finite and ψ maps inl into inl
          choose τf hτf using hψ_inl
          have hτ_inj : Function.Injective τf := by
            intro x y h
            exact Sum.inl.inj (ψ.injective (by rw [hτf, hτf, h]))
          have hτ_surj : Function.Surjective τf := (Finite.injective_iff_surjective.mp hτ_inj)
          obtain ⟨b', hb'⟩ := hτ_surj a
          have hcoll : ψ (Sum.inl b') = ψ (Sum.inr b) := by rw [hτf b', hb', hval]
          exact False.elim (Sum.inl_ne_inr (ψ.injective hcoll))
        | inr a => exact ⟨a, rfl⟩
      choose τ₁f hτ₁ using hψ_inl
      choose τ₂f hτ₂ using hψ_inr
      have h₁inj : Function.Injective τ₁f := fun x y h =>
        Sum.inl.inj (ψ.injective (by rw [hτ₁, hτ₁, h]))
      have h₂inj : Function.Injective τ₂f := fun x y h =>
        Sum.inr.inj (ψ.injective (by rw [hτ₂, hτ₂, h]))
      let τ₁ := Equiv.ofBijective τ₁f (Finite.injective_iff_bijective.mp h₁inj)
      let τ₂ := Equiv.ofBijective τ₂f (Finite.injective_iff_bijective.mp h₂inj)
      refine ⟨(τ₁, τ₂), Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      apply Equiv.ext; intro x
      have hψeq : Equiv.sumCongr τ₁ τ₂ = ψ := by
        apply Equiv.ext; intro s
        cases s with
        | inl b => exact (hτ₁ b).symm
        | inr b => exact (hτ₂ b).symm
      change e (Equiv.sumCongr τ₁ τ₂ (e.symm x)) = σ x
      rw [hψeq]; simp [ψ]
    · rintro ⟨τ₁, τ₂⟩ _
      have hpe : (∏ b : Fin k, M (Φ (τ₁, τ₂) b) b) =
          ∏ s : Fin k1 ⊕ Fin k2, M (Φ (τ₁, τ₂) (e s)) (e s) :=
        (Equiv.prod_comp e (fun b => M (Φ (τ₁, τ₂) b) b)).symm
      rw [hpe, Fintype.prod_sum_type]
      congr 1
      · refine Finset.prod_congr rfl fun b _ => ?_
        have : Φ (τ₁, τ₂) (e (Sum.inl b)) = e (Sum.inl (τ₁ b)) := by simp [Φ]
        rw [this, hM_inl_inl]
      · refine Finset.prod_congr rfl fun b _ => ?_
        have : Φ (τ₁, τ₂) (e (Sum.inr b)) = e (Sum.inr (τ₂ b)) := by simp [Φ]
        rw [this, hM_inr_inr]
  rw [hsum, Fintype.sum_prod_type, Matrix.permanent, Matrix.permanent]
  simp only [Matrix.of_apply, ← Finset.mul_sum, ← Finset.sum_mul]

private def subSum {p q : ℕ} (t : Fin p × Fin q → ℂ) (k : ℕ) : ℂ :=
  ∑ R : Finset (Fin p), ∑ C : Finset (Fin q),
    if h : R.card = k ∧ C.card = k then
      Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
    else 0

private lemma subSum_zero_of_gt {p q : ℕ} (t : Fin p × Fin q → ℂ) (k : ℕ) (hgt : min p q < k) :
    subSum t k = 0 := by
  unfold subSum
  refine Finset.sum_eq_zero fun R _ => Finset.sum_eq_zero fun C _ => ?_
  rw [dite_eq_right]
  intro ⟨hR, hC⟩
  have hRp : R.card ≤ p := by simpa using Finset.card_le_univ R
  have hCq : C.card ≤ q := by simpa using Finset.card_le_univ C
  omega

theorem main (p1 q1 p2 q2 : ℕ)
    (L1 : Submodule ℂ (Fin p1 × Fin q1 → ℂ))
    (L2 : Submodule ℂ (Fin p2 × Fin q2 → ℂ))
    (hL1 : ∀ t ∈ L1, ∀ k : ℕ, 1 ≤ k → k ≤ min p1 q1 → subSum t k = 0)
    (hL2 : ∀ t ∈ L2, ∀ k : ℕ, 1 ≤ k → k ≤ min p2 q2 → subSum t k = 0)
    (t1 : Fin p1 × Fin q1 → ℂ) (ht1 : t1 ∈ L1)
    (t2 : Fin p2 × Fin q2 → ℂ) (ht2 : t2 ∈ L2)
    (T : Fin (p1 + p2) × Fin (q1 + q2) → ℂ)
    (hT : ∀ x, T x = Matrix.fromBlocks (Matrix.of fun a b => t1 (a, b)) 0 0
        (Matrix.of fun a b => t2 (a, b)) (finSumFinEquiv.symm x.1) (finSumFinEquiv.symm x.2))
    (k : ℕ) (hk1 : 1 ≤ k) (_hk2 : k ≤ min (p1 + p2) (q1 + q2)) :
    subSum T k = 0 := by
  have hsplit : subSum T k = ∑ k1 ∈ Finset.range (k + 1), subSum t1 k1 * subSum t2 (k - k1) := by
    unfold subSum
    rw [← Equiv.sum_comp (splitFinsetEquiv p1 p2).symm]
    simp_rw [← Equiv.sum_comp (splitFinsetEquiv q1 q2).symm]
    have hterm : ∀ (pR : Finset (Fin p1) × Finset (Fin p2)) (pC : Finset (Fin q1) × Finset (Fin q2)),
        (if h : (combine pR.1 pR.2).card = k ∧ (combine pC.1 pC.2).card = k then
          Matrix.permanent (Matrix.of fun a b =>
            T ((combine pR.1 pR.2).orderEmbOfFin h.1 a, (combine pC.1 pC.2).orderEmbOfFin h.2 b))
        else 0) =
        ∑ k1 ∈ Finset.range (k + 1),
          (if h1 : pR.1.card = k1 ∧ pC.1.card = k1 then
            Matrix.permanent (Matrix.of fun a b => t1 (pR.1.orderEmbOfFin h1.1 a, pC.1.orderEmbOfFin h1.2 b))
          else 0) *
          (if h2 : pR.2.card = k - k1 ∧ pC.2.card = k - k1 then
            Matrix.permanent (Matrix.of fun a b => t2 (pR.2.orderEmbOfFin h2.1 a, pC.2.orderEmbOfFin h2.2 b))
          else 0) := by
      rintro ⟨R1, R2⟩ ⟨C1, C2⟩
      by_cases hcond : (combine R1 R2).card = k ∧ (combine C1 C2).card = k
      · rw [dif_pos hcond]
        by_cases heqc : R1.card = C1.card
        · have hkR : R1.card + R2.card = k := by rw [← card_combine, hcond.1]
          have hkC : C1.card + C2.card = k := by rw [← card_combine, hcond.2]
          have hmem : R1.card ∈ Finset.range (k + 1) := by rw [Finset.mem_range]; omega
          rw [Finset.sum_eq_single R1.card]
          · have hR2 : R2.card = k - R1.card := by omega
            have hC2 : C2.card = k - R1.card := by omega
            simp only [heqc.symm, hR2, hC2, and_self, ↓reduceDIte]
            exact perm_block_eq t1 t2 T hT R1 R2 C1 C2 rfl hR2 heqc.symm hC2 hcond.1 hcond.2 (by omega)
          · intro k1 _ hne
            have hnot1 : ¬ (R1.card = k1 ∧ C1.card = k1) := fun h => hne h.1.symm
            simp [hnot1]
          · intro hnot; exact False.elim (hnot hmem)
        · rw [perm_block_ne t1 t2 T hT R1 R2 C1 C2 hcond.1 hcond.2 heqc]
          symm
          refine Finset.sum_eq_zero fun k1 _ => ?_
          have hnot1 : ¬ (R1.card = k1 ∧ C1.card = k1) := fun h => heqc (h.1.trans h.2.symm)
          simp [hnot1]
      · rw [dif_neg hcond]
        symm
        refine Finset.sum_eq_zero fun k1 hk1m => ?_
        by_cases h1 : R1.card = k1 ∧ C1.card = k1
        · have hnot2 : ¬ (R2.card = k - k1 ∧ C2.card = k - k1) := by
            intro h2
            apply hcond
            have hk1le : k1 ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk1m)
            exact ⟨by rw [card_combine, h1.1, h2.1]; omega, by rw [card_combine, h1.2, h2.2]; omega⟩
          simp [hnot2]
        · simp [h1]
    have hrew :
        (∑ pR : Finset (Fin p1) × Finset (Fin p2), ∑ pC : Finset (Fin q1) × Finset (Fin q2),
          if h : ((splitFinsetEquiv p1 p2).symm pR).card = k ∧ ((splitFinsetEquiv q1 q2).symm pC).card = k then
            Matrix.permanent (Matrix.of fun a b =>
              T (((splitFinsetEquiv p1 p2).symm pR).orderEmbOfFin h.1 a,
                 ((splitFinsetEquiv q1 q2).symm pC).orderEmbOfFin h.2 b))
          else 0) =
        ∑ pR : Finset (Fin p1) × Finset (Fin p2), ∑ pC : Finset (Fin q1) × Finset (Fin q2),
          ∑ k1 ∈ Finset.range (k + 1),
            (if h1 : pR.1.card = k1 ∧ pC.1.card = k1 then
              Matrix.permanent (Matrix.of fun a b => t1 (pR.1.orderEmbOfFin h1.1 a, pC.1.orderEmbOfFin h1.2 b))
            else 0) *
            (if h2 : pR.2.card = k - k1 ∧ pC.2.card = k - k1 then
              Matrix.permanent (Matrix.of fun a b => t2 (pR.2.orderEmbOfFin h2.1 a, pC.2.orderEmbOfFin h2.2 b))
            else 0) :=
      Finset.sum_congr rfl fun pR _ => Finset.sum_congr rfl fun pC _ => hterm pR pC
    rw [hrew]
    have hswap1 : ∀ pR : Finset (Fin p1) × Finset (Fin p2),
        (∑ pC : Finset (Fin q1) × Finset (Fin q2), ∑ k1 ∈ Finset.range (k + 1),
          (if h1 : pR.1.card = k1 ∧ pC.1.card = k1 then
            Matrix.permanent (Matrix.of fun a b => t1 (pR.1.orderEmbOfFin h1.1 a, pC.1.orderEmbOfFin h1.2 b))
          else 0) *
          (if h2 : pR.2.card = k - k1 ∧ pC.2.card = k - k1 then
            Matrix.permanent (Matrix.of fun a b => t2 (pR.2.orderEmbOfFin h2.1 a, pC.2.orderEmbOfFin h2.2 b))
          else 0)) =
        ∑ k1 ∈ Finset.range (k + 1), ∑ pC : Finset (Fin q1) × Finset (Fin q2),
          (if h1 : pR.1.card = k1 ∧ pC.1.card = k1 then
            Matrix.permanent (Matrix.of fun a b => t1 (pR.1.orderEmbOfFin h1.1 a, pC.1.orderEmbOfFin h1.2 b))
          else 0) *
          (if h2 : pR.2.card = k - k1 ∧ pC.2.card = k - k1 then
            Matrix.permanent (Matrix.of fun a b => t2 (pR.2.orderEmbOfFin h2.1 a, pC.2.orderEmbOfFin h2.2 b))
          else 0) := fun _ => Finset.sum_comm
    simp_rw [hswap1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k1 _ => ?_
    simp only [Fintype.sum_prod_type]
    have hfactor : ∀ (R1 : Finset (Fin p1)),
        (∑ R2 : Finset (Fin p2), ∑ C1 : Finset (Fin q1), ∑ C2 : Finset (Fin q2),
          (if h1 : R1.card = k1 ∧ C1.card = k1 then
            Matrix.permanent (Matrix.of fun a b => t1 (R1.orderEmbOfFin h1.1 a, C1.orderEmbOfFin h1.2 b))
          else 0) *
          (if h2 : R2.card = k - k1 ∧ C2.card = k - k1 then
            Matrix.permanent (Matrix.of fun a b => t2 (R2.orderEmbOfFin h2.1 a, C2.orderEmbOfFin h2.2 b))
          else 0)) =
        (∑ C1 : Finset (Fin q1),
          if h1 : R1.card = k1 ∧ C1.card = k1 then
            Matrix.permanent (Matrix.of fun a b => t1 (R1.orderEmbOfFin h1.1 a, C1.orderEmbOfFin h1.2 b))
          else 0) *
        (∑ R2 : Finset (Fin p2), ∑ C2 : Finset (Fin q2),
          if h2 : R2.card = k - k1 ∧ C2.card = k - k1 then
            Matrix.permanent (Matrix.of fun a b => t2 (R2.orderEmbOfFin h2.1 a, C2.orderEmbOfFin h2.2 b))
          else 0) := by
      intro R1
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    simp_rw [hfactor]
    rw [← Finset.sum_mul]
  rw [hsplit]
  refine Finset.sum_eq_zero fun k1 hk1m => ?_
  by_cases h0 : k1 = 0
  · subst h0
    simp only [Nat.sub_zero]
    by_cases hle : k ≤ min p2 q2
    · rw [hL2 t2 ht2 k hk1 hle, mul_zero]
    · rw [subSum_zero_of_gt t2 k (by omega), mul_zero]
  · have hk1pos : 1 ≤ k1 := Nat.one_le_iff_ne_zero.mpr h0
    by_cases hle : k1 ≤ min p1 q1
    · rw [hL1 t1 ht1 k1 hk1pos hle, zero_mul]
    · rw [subSum_zero_of_gt t1 k1 (by omega), zero_mul]

end PEqualNP.Outside.Gct204

theorem PEqualNP.Outside.L_gct_204 : ∀ p1 q1 p2 q2 : ℕ, ∀ L1 : Submodule ℂ (Fin p1 × Fin q1 → ℂ), ∀ L2 : Submodule ℂ (Fin p2 × Fin q2 → ℂ), (∀ t ∈ L1, ∀ k : ℕ, 1 ≤ k → k ≤ min p1 q1 → (∑ R : Finset (Fin p1), ∑ C : Finset (Fin q1), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) → (∀ t ∈ L2, ∀ k : ℕ, 1 ≤ k → k ≤ min p2 q2 → (∑ R : Finset (Fin p2), ∑ C : Finset (Fin q2), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) → ∀ t1 ∈ L1, ∀ t2 ∈ L2, ∀ T : Fin (p1 + p2) × Fin (q1 + q2) → ℂ, (∀ x, T x = Matrix.fromBlocks (Matrix.of fun a b => t1 (a, b)) 0 0 (Matrix.of fun a b => t2 (a, b)) (finSumFinEquiv.symm x.1) (finSumFinEquiv.symm x.2)) → ∀ k : ℕ, 1 ≤ k → k ≤ min (p1 + p2) (q1 + q2) → (∑ R : Finset (Fin (p1 + p2)), ∑ C : Finset (Fin (q1 + q2)), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => T (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0 :=
  PEqualNP.Outside.Gct204.main
