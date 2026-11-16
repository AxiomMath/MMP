module

import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.Divisor.SmoothDivisorAdjunction
import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor
import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
public import MMP.AlgebraicGeometry.Resolution.SmoothCentreBlowup
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier

/-!
# Positivity of intersection numbers and restriction to smooth divisors

This file collects the facts about intersection numbers and about restricting divisors to a smooth
prime divisor that enter the proof of the nonvanishing and Kawamata–Viehweg arguments of
Kollár–Mori, Chapter 3, together with the multiplicity of a pulled-back divisor along the
exceptional divisor of a point blow-up.

Let `X` be a projective variety of dimension `d` over a field `k`. If `L` is nef and `A` ample,
the mixed intersection numbers `(L^e · A^{d-e})` are nonnegative; expanding `((tD + H)^d)`
multilinearly, with `D` nef and `H` ample, gives `((tD + H)^d) ≥ d · t · (D · H^{d-1})`.

Let `Y` be a smooth variety and `F ⊆ Y` a smooth prime divisor with closed immersion `ι`. For a
divisor `B` of which `F` is not a component, the restriction `B|_F` is the pull-back `ι^* B`: it
is Cartier, `𝒪_F(B|_F) ≅ ι^* 𝒪_Y(B)`, and restrictions of local equations of `B` are local
equations of `B|_F`. When `H¹(Y, 𝒪_Y(K + N)) = 0`, sections of `𝒪_Y(K + N + F)` restrict onto
those of `ι^* 𝒪_Y(K + N + F) ≅ ω_F ⊗ ι^* 𝒪_Y(N)`. If `F + ∑ Dᵢ` is snc, then `(∑ Dᵢ)|_F` is a
reduced snc divisor, and round-up commutes with restriction to `F`.

Finally, on the blow-up `π : B_x X ⟶ X` of a closed point of a smooth variety, the coefficient of
the exceptional divisor in `π^* P` is the order at `x` of a local equation of `P`.

## Main results

* `MMP.Mori.sheafPowIntersectionNumber_nonneg_of_isNef_of_isAmple`: `(L^e · A^{d-e}) ≥ 0`.
* `MMP.Mori.mul_intersectionNumber_cons_le_intersectionNumber_smul_add`:
  `d · t · (D · H^{d-1}) ≤ ((tD + H)^d)`.
* `MMP.Mori.Divisor.isCartier_restrictPrimeDivisor_of_isSmoothVariety`: `B|_F` is Cartier, with
  divisorial sheaf `ι^* 𝒪_Y(B)` and local equations the restrictions of those of `B`.
* `MMP.Mori.Divisor.surjective_cohomologyOverFieldMap_restriction`: on a smooth variety,
  `H¹(Y, 𝒪_Y(D)) = 0` makes `H⁰(Y, 𝒪_Y(D + F)) ⟶ H⁰(F, ι^* 𝒪_Y(D + F))` surjective.
* `MMP.Mori.Divisor.nonempty_pullback_divisorialSheaf_iso_of_isCanonicalDivisor`: adjunction
  `ι^* 𝒪_Y(K + N + F) ≅ Ω^n_F ⊗ ι^* 𝒪_Y(N)` for a Cartier divisor `N`.
* `MMP.Mori.Divisor.surjective_restriction_of_subsingleton_cohomologyOverField_one`: surjectivity
  of the restriction of adjoint sections, and adjunction `ι^* 𝒪_Y(K + N + F) ≅ ω_F ⊗ ι^* 𝒪_Y(N)`.
* `MMP.Mori.DivisorWithCoeffs.isSNC_restrictPrimeDivisor_sum_single`: `(∑ Dᵢ)|_F` is snc and
  reduced.
* `MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor_roundUp`: `⌈D⌉|_F = ⌈D|_F⌉`.
* `MMP.Threefold.Resolution.coeff_exceptional_eq_maximalIdealOrder_of_isPullback`: the
  exceptional coefficient of `π^* P` is `MMP.Flips.maximalIdealOrder` of a local equation of `P`.

## Implementation notes

Intersection numbers are those of families of invertible sheaves against the identity of `X`;
Cartier divisors enter through `MMP.CartierDivisor.sheaf`, so no normality of `X`
is needed. The expansion of `((tD + H)^d)` is an induction over the set of slots still carrying
`tD + H`, keeping only the terms with at most one `D`. The restriction `B|_F` is
`MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor`, defined by local intersection lengths; if
`F + ∑_{E ∈ S} E` is snc, these lengths sum to at most one along every prime divisor of `F`, which
drives both the snc and the round-up statements. In the round-up statement the coefficients lie in
any ordered floor ring, the source's `ℚ` being one case.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.38, 3.5,
  3.9–3.10
-/

universe u v

namespace MMP.Mori

section Positivity

open CategoryTheory AlgebraicGeometry

/-- **Mixed powers of a nef and an ample invertible sheaf are nonnegative.** On a projective
variety `X` of dimension `d` over a field `k`, a nef invertible sheaf `L` and an ample invertible
sheaf `A` satisfy `(L^e · A^{d-e}) ≥ 0` for every `e ≤ d`. -/
@[mmp "lem_mmp_nef_ample_mixed_nonnegative"]
public theorem sheafPowIntersectionNumber_nonneg_of_isNef_of_isAmple (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] {d : ℕ}
    (hdim : topologicalKrullDim X = d) (L A : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    (hL : IsNef k sX L) (hA : Stacks.Ample.IsAmple X A) {e : ℕ} (he : e ≤ d) :
    haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![L, A] t) := by
      intro t; fin_cases t <;> assumption
    0 ≤ sheafPowIntersectionNumber k sX (𝟙 X) ![e, d - e]
      (by rw [hdim]; exact_mod_cast (show d ≤ ∑ t, ![e, d - e] t by simp; omega)) ![L, A] :=
  MMP.Threefold.Mori.sheafPowIntersectionNumber_nonneg_of_isAmple k sX ‹_› hdim L A hA he
    fun W i _ _ hW => sheafSelfIntersectionNumber_nonneg_of_isNef k sX ‹_› L hL W i hW

section DivNum

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX] {d : ℕ}
  (hd : topologicalKrullDim X ≤ d)

/-- The intersection number of a family of Cartier divisors. -/
private noncomputable abbrev divNum (Ψ : Fin d → X.CartierDivisor) : ℤ :=
  intersectionNumber k sX (𝟙 X) d hd fun j => MMP.CartierDivisor.sheaf (Ψ j)

private theorem divNum_update_add (Ψ : Fin d → X.CartierDivisor) (j : Fin d)
    (A B : X.CartierDivisor) :
    divNum k sX hd (Function.update Ψ j (A + B)) =
      divNum k sX hd (Function.update Ψ j A) + divNum k sX hd (Function.update Ψ j B) :=
  intersectionNumber_tensor k sX (𝟙 X) d hd j _ _ _
    (fun q hq => by simp [Function.update_of_ne hq])
    (fun q hq => by simp [Function.update_of_ne hq])
    (eqToIso (by simp) ≪≫ (MMP.CartierDivisorSheaf.sheafMulIso A B).symm ≪≫
      eqToIso (by simp; rfl))

private theorem divNum_update_nsmul (Ψ : Fin d → X.CartierDivisor) (j : Fin d)
    (D : X.CartierDivisor) (t : ℕ) :
    divNum k sX hd (Function.update Ψ j (t • D)) = t * divNum k sX hd (Function.update Ψ j D) := by
  induction t with
  | zero => simpa using divNum_update_add k sX hd Ψ j 0 0
  | succ t ih => rw [succ_nsmul, divNum_update_add, ih]; push_cast; ring

private theorem divNum_comp_perm (Ψ : Fin d → X.CartierDivisor) (σ : Equiv.Perm (Fin d)) :
    divNum k sX hd (Ψ ∘ σ) = divNum k sX hd Ψ :=
  intersectionNumber_comp_perm k sX (𝟙 X) d hd
    (fun j => MMP.CartierDivisor.sheaf (Ψ j)) σ

/-- Two-valued families depend only on the number of slots carrying the first value. -/
private theorem divNum_ite_mem (D H : X.CartierDivisor) (S : Finset (Fin d)) :
    divNum k sX hd (fun j => if j ∈ S then D else H) =
      divNum k sX hd (fun j => if (j : ℕ) < S.card then D else H) := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
    (Finset.univ.filter fun j : Fin d => (j : ℕ) < S.card) S (by
      have : S.card ≤ d := by simpa using S.card_le_univ
      simp [Fin.card_filter_val_lt, this])
  rw [← divNum_comp_perm k sX hd _ σ]
  congr 1
  funext j
  have : σ j ∈ S ↔ (j : ℕ) < S.card := by
    have h := Finset.mem_map' σ.toEmbedding
      (s := Finset.univ.filter fun j : Fin d => (j : ℕ) < S.card) (a := j)
    rw [hσ] at h
    simpa using h
  simp [Function.comp, this]

variable {k sX hd} in
/-- The expansion of `((tD + H)^d)` slot by slot, keeping the terms with at most one `D`. -/
private theorem le_divNum_fam (D H : X.CartierDivisor) (t : ℕ) (α : ℤ)
    (hmix : ∀ S : Finset (Fin d), 0 ≤ divNum k sX hd (fun j => if j ∈ S then D else H))
    (hone : ∀ S : Finset (Fin d), S.card = 1 →
      divNum k sX hd (fun j => if j ∈ S then D else H) = α)
    (S₀ : Finset (Fin d)) : ∀ S₁ : Finset (Fin d), Disjoint S₀ S₁ →
      (if S₁.card = 0 then (t : ℤ) * S₀.card * α else if S₁.card = 1 then α else 0) ≤
        divNum k sX hd
          (fun j => if j ∈ S₀ then t • D + H else if j ∈ S₁ then D else H) := by
  classical
  induction S₀ using Finset.induction_on with
  | empty =>
    intro S₁ _
    simp only [Finset.notMem_empty, if_false, Finset.card_empty, Nat.cast_zero, mul_zero,
      zero_mul]
    split_ifs with h0 h1
    · exact hmix S₁
    · exact (hone S₁ h1).ge
    · exact hmix S₁
  | insert a s ha ih =>
    intro S₁ hdisj
    have haS₁ : a ∉ S₁ := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a s)
    have hs : Disjoint s S₁ := Finset.disjoint_of_subset_left (Finset.subset_insert a s) hdisj
    have hs' : Disjoint s (insert a S₁) := Finset.disjoint_insert_right.mpr ⟨ha, hs⟩
    set Ψ : Fin d → X.CartierDivisor :=
      fun j => if j ∈ s then t • D + H else if j ∈ S₁ then D else H with hΨ
    have e0 : (fun j => if j ∈ insert a s then t • D + H else if j ∈ S₁ then D else H) =
        Function.update Ψ a (t • D + H) := by
      funext j
      by_cases hj : j = a
      · subst hj; simp
      · simp [Function.update_of_ne hj, hΨ, hj]
    have e1 : Function.update Ψ a D =
        fun j => if j ∈ s then t • D + H else if j ∈ insert a S₁ then D else H := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [ha]
      · simp [Function.update_of_ne hj, hΨ, hj]
    have e2 : Function.update Ψ a H = Ψ := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [hΨ, ha, haS₁]
      · simp [Function.update_of_ne hj]
    rw [e0, divNum_update_add, divNum_update_nsmul, e1, e2]
    have h1 := ih (insert a S₁) hs'
    have h2 := ih S₁ hs
    rw [Finset.card_insert_of_notMem haS₁] at h1
    rw [Finset.card_insert_of_notMem ha]
    have ht : (0 : ℤ) ≤ t := by positivity
    rcases Nat.lt_or_ge S₁.card 2 with hc | hc
    · interval_cases hc' : S₁.card
      · simp only [if_true, zero_add, if_false, one_ne_zero] at h1 h2 ⊢
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left h1 ht]
      · simp only [if_true, if_false, one_ne_zero, show (1 : ℕ) + 1 ≠ 0 by omega,
          show (1 : ℕ) + 1 ≠ 1 by omega] at h1 h2 ⊢
        nlinarith [mul_le_mul_of_nonneg_left h1 ht]
    · simp only [show S₁.card ≠ 0 by omega, show S₁.card ≠ 1 by omega, if_false,
        show S₁.card + 1 ≠ 0 by omega, show S₁.card + 1 ≠ 1 by omega] at h1 h2 ⊢
      nlinarith [mul_le_mul_of_nonneg_left h1 ht]

variable {k sX} in
private theorem intersectionNumber_eq_of_cast {m : ℕ} (h : m = d)
    (hm : topologicalKrullDim X ≤ m) (F : Fin m → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F j)] (G : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (G j)]
    (hFG : ∀ t, F t = G (Fin.cast h t)) :
    intersectionNumber k sX (𝟙 X) m hm F = intersectionNumber k sX (𝟙 X) d hd G := by
  subst h
  obtain rfl : F = G := funext fun t => by simpa using hFG t
  rfl

/-- A two-valued family with the first value in the first `e` slots computes the mixed
intersection number `(𝒪(D)^e · 𝒪(H)^{d-e})`. -/
private theorem divNum_ite_lt_eq_sheafPowIntersectionNumber (D H : X.CartierDivisor) {e : ℕ}
    (he : e ≤ d) (hd' : topologicalKrullDim X ≤ ∑ j, ![e, d - e] j) :
    haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (![MMP.CartierDivisor.sheaf D,
          MMP.CartierDivisor.sheaf H] t) := by
      intro t; fin_cases t <;> simp <;> infer_instance
    divNum k sX hd (fun j => if (j : ℕ) < e then D else H) =
      sheafPowIntersectionNumber k sX (𝟙 X) ![e, d - e] hd'
        ![MMP.CartierDivisor.sheaf D,
          MMP.CartierDivisor.sheaf H] := by
  have hsum : ∑ j, ![e, d - e] j = d := by simp; omega
  haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![MMP.CartierDivisor.sheaf D,
        MMP.CartierDivisor.sheaf H] t) := by
    intro t; fin_cases t <;> simp <;> infer_instance
  rw [sheafPowIntersectionNumber, Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  refine (intersectionNumber_eq_of_cast hd hsum _ _ _ fun t => ?_).symm
  obtain ⟨⟨i, b⟩, rfl⟩ := finSigmaFinEquiv.surjective t
  rw [Equiv.symm_apply_apply]
  fin_cases i
  · have hb : (b : ℕ) < e := by simpa using b.2
    simp [hb]
  · have hb : ¬ (e + (b : ℕ) < e) := by omega
    simp [Fin.sum_univ_succ, hb]

end DivNum

/-- **The top self-intersection of `tD + H` grows at least linearly in `t`** (Kollár–Mori 3.5,
Step 2). On a projective variety `X` of dimension `n + 1` over `k`, for a nef Cartier divisor `D`,
an ample Cartier divisor `H` and `t : ℕ`, `(n + 1) · t · (D · H^n) ≤ ((tD + H)^{n+1})`. -/
@[mmp "lem_km3a_nonvanishing_top_self_intersection_grows"]
public theorem mul_intersectionNumber_cons_le_intersectionNumber_smul_add (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ)) (D H : X.CartierDivisor)
    (hD : IsNef k sX (MMP.CartierDivisor.sheaf D))
    (hH : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf H)) (t : ℕ) :
    ((n + 1 : ℕ) : ℤ) * t * intersectionNumber k sX (𝟙 X) (n + 1) hdim.le
        (fun j => MMP.CartierDivisor.sheaf
          ((Fin.cons D fun _ => H : Fin (n + 1) → X.CartierDivisor) j)) ≤
      intersectionNumber k sX (𝟙 X) (n + 1) hdim.le
        fun _ => MMP.CartierDivisor.sheaf (t • D + H) := by
  classical
  set α := divNum k sX hdim.le (Fin.cons D fun _ => H : Fin (n + 1) → X.CartierDivisor)
  have hmix : ∀ S : Finset (Fin (n + 1)),
      0 ≤ divNum k sX hdim.le (fun j => if j ∈ S then D else H) := by
    intro S
    have he : S.card ≤ n + 1 := by simpa using S.card_le_univ
    rw [divNum_ite_mem, divNum_ite_lt_eq_sheafPowIntersectionNumber k sX hdim.le D H he
      (by rw [hdim]; exact_mod_cast (show n + 1 ≤ ∑ j, ![S.card, n + 1 - S.card] j by
        simp; omega))]
    exact MMP.Mori.sheafPowIntersectionNumber_nonneg_of_isNef_of_isAmple k sX hdim _ _ hD hH he
  have hone : ∀ S : Finset (Fin (n + 1)), S.card = 1 →
      divNum k sX hdim.le (fun j => if j ∈ S then D else H) = α := by
    intro S hS
    rw [divNum_ite_mem, hS]
    congr 1
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  have key := le_divNum_fam D H t α hmix hone Finset.univ ∅ (Finset.disjoint_empty_right _)
  simp only [Finset.card_empty, if_true, Finset.card_univ, Fintype.card_fin,
    Finset.mem_univ, if_true] at key
  linarith

end Positivity

end MMP.Mori

namespace MMP.Mori.Divisor

section Restriction

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

section Pullback

open Classical

/-- The generic point of an irreducible component has coheight zero. -/
private theorem coheight_componentGenericPoint {X : Scheme.{u}} (Z : irreducibleComponents X) :
    Order.coheight (componentGenericPoint X Z) = 0 := by
  rw [Order.coheight_eq_zero]
  intro b (hb : b ⤳ _)
  have hZ := (isGenericPoint_componentGenericPoint X Z).def
  refine specializes_iff_closure_subset.mpr ?_
  rw [hZ]
  exact Z.2.2 isIrreducible_singleton.closure (hZ ▸ hb.closure_subset)

/-- In an irreducible space there is only one irreducible component. -/
private theorem irreducibleComponents_eq {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    (Z W : irreducibleComponents X) : Z = W :=
  Subtype.ext <| by
    have hZ := Z.2; have hW := W.2
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ hW
    rw [hZ, hW]

/-- On an integral scheme, `v_Γ` of a unit of the function field of the component is the
order of vanishing `AlgebraicGeometry.Scheme.ord` of its image in the function field. -/
private theorem ordUnit_eq_ord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (Γ : MMP.Mori.PrimeDivisor X)
    (v : (X.presheaf.stalk (componentGenericPoint X Γ.component))ˣ) :
    Γ.ordUnit v = X.ord ((X.presheaf.stalkSpecializes
        (((genericPoint_spec X).specializes trivial :
          genericPoint X ⤳ componentGenericPoint X Γ.component))).hom v) Γ.genericPoint := by
  set g := (X.presheaf.stalkSpecializes
        (((genericPoint_spec X).specializes trivial :
          genericPoint X ⤳ componentGenericPoint X Γ.component))).hom
  have hne : g v ≠ 0 := (v.isUnit.map g).ne_zero
  symm
  rw [Scheme.ord_eq_iff Γ.coheight_genericPoint hne]
  have : Ring.KrullDimLE 1 Γ.localRing := krullDimLE_of_coheight_le Γ.coheight_genericPoint.le
  have h := Γ.valuation_eq_exp_ordUnit v
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac] at h
  unfold Scheme.ordHom
  convert h using 1
  rfl

variable {k : Type u} [Field k] {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [Smooth sY] (j : T ⟶ Y) [IsClosedImmersion j]
  [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [Smooth (j ≫ sY)]

include sY in
/-- **Restricting a quotient of germs.** Let `Q` be a prime divisor of `T` and `a, b ∈ 𝒪_{Y,y}`,
`y = j(η_Q)`, with nonzero restrictions to `𝒪_{T,Q}`. If `D` has coefficient
`v_E(a) - v_E(b)` along every prime divisor `E` of `Y` through `y`, then
`∑_E length(𝒪_{T,Q}/I_E 𝒪_{T,Q}) · D_E = v_Q(a|_T) - v_Q(b|_T)`. -/
private theorem sum_intersectionLength_smul_eq_ord_sub (Q : MMP.Mori.PrimeDivisor T)
    (D : Divisor Y) (a b : Y.presheaf.stalk (j Q.genericPoint))
    (ha : (j.stalkMap Q.genericPoint).hom a ≠ 0) (hb : (j.stalkMap Q.genericPoint).hom b ≠ 0)
    (hD : ∀ E : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ E.support →
      D.coeff E = Y.ord (algebraMap _ Y.functionField a) E.genericPoint -
        Y.ord (algebraMap _ Y.functionField b) E.genericPoint) :
    (D.sum fun E d => E.intersectionLength j Q • d) =
      T.ord (algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom a)) Q.genericPoint -
        T.ord (algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom b))
          Q.genericPoint := by
  obtain ⟨Sa, -, hfa⟩ := Q.ord_stalkMap_eq_sum_intersectionLength_mul_ord sY j a ha
  obtain ⟨Sb, -, hfb⟩ := Q.ord_stalkMap_eq_sum_intersectionLength_mul_ord sY j b hb
  set S := D.support ∪ Sa ∪ Sb
  rw [hfa S (by intro E hE; simp [S, hE]), hfb S (by intro E hE; simp [S, hE]),
    ← Finset.sum_sub_distrib, Finsupp.sum, Finset.sum_subset (s₂ := S)
      (by intro E hE; simp [S, hE]) (by intro E _ hE; simp [Finsupp.notMem_support_iff.mp hE])]
  refine Finset.sum_congr rfl fun E _ => ?_
  split_ifs with hE
  · rw [nsmul_eq_mul, ← mul_sub, ← hD E hE]; rfl
  · rw [MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem j E hE, zero_smul, sub_zero]

include sY in
/-- **A divisor with intersection-length coefficients is the pull-back.** If the coefficient of
every prime divisor `Q` of `T` in `D` is `∑_E B_E · length(𝒪_{T,Q}/I_E 𝒪_{T,Q})`, then `D` is the
pull-back `j^* B`. -/
public theorem isPullback_of_coeff_eq (B : Divisor Y)
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ B.supp)
    (D : Divisor T)
    (hD : ∀ Q : MMP.Mori.PrimeDivisor T,
      D.coeff Q = B.sum fun E d => E.intersectionLength j Q • d) :
    B.IsPullback j hB D := by
  intro U h hh Q hQ
  set x := componentGenericPoint T Q.component
  have hx : j x ∈ U := Q.map_componentGenericPoint_mem j hQ
  have hspT : x ⤳ Q.genericPoint :=
    (isGenericPoint_componentGenericPoint T Q.component).specializes Q.genericPoint_mem_component
  have hspY : j x ⤳ j Q.genericPoint := j.base.hom.map_specializes hspT
  have hyU : j Q.genericPoint ∈ U := (Q.genericPoint_mem_iff (j ⁻¹ᵁ U)).mpr hQ
  -- the unit `a₀` of `𝒪_{Y, j x}` representing `h`
  set a₀ := (hh.exists_unit_stalk hx (hB Q.component) (mem_pointComponent _)).choose with ha₀
  have ha₀spec := (hh.exists_unit_stalk hx (hB Q.component) (mem_pointComponent _)).choose_spec
  rw [← ha₀] at ha₀spec
  have hc : pullbackComponent j hB hh Q.component hx =
      Units.map (j.stalkMap x).hom.toMonoidHom a₀ := rfl
  -- write `a₀ = r / s` with `r, s ∈ 𝒪_{Y,y}`, `s` outside the prime of `F` at `y`
  let q : PrimeSpectrum (Y.presheaf.stalk (j Q.genericPoint)) :=
    ⟨MMP.Intersection.primeOfSpecializes hspY, inferInstance⟩
  letI : Algebra (Y.presheaf.stalk (j Q.genericPoint)) (Y.presheaf.stalk (j x)) :=
    (Y.presheaf.stalkSpecializes hspY).hom.toAlgebra
  haveI := Stacks.Chow.isLocalization_stalk_of_specializes hspY q
    (MMP.Intersection.fromSpecStalk_primeOfSpecializes hspY)
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl
    (a₀ : Y.presheaf.stalk (j x))
  have hrs' : (a₀ : Y.presheaf.stalk (j x)) * Y.presheaf.stalkSpecializes hspY s =
      Y.presheaf.stalkSpecializes hspY r := by
    rw [← hrs]; exact IsLocalization.mk'_spec _ r s
  have hsu : IsUnit (Y.presheaf.stalkSpecializes hspY (s : Y.presheaf.stalk (j Q.genericPoint))) :=
    IsLocalization.map_units (Y.presheaf.stalk (j x)) s
  have hru : IsUnit (Y.presheaf.stalkSpecializes hspY (r : Y.presheaf.stalk (j Q.genericPoint))) :=
    hrs' ▸ a₀.isUnit.mul hsu
  have key : ∀ t, (j.stalkMap x).hom (Y.presheaf.stalkSpecializes hspY t) =
      T.presheaf.stalkSpecializes hspT ((j.stalkMap Q.genericPoint).hom t) := fun t =>
    j.stalkSpecializes_stalkMap_apply x Q.genericPoint hspT t
  have hne0 : ∀ t, IsUnit (Y.presheaf.stalkSpecializes hspY t) →
      (j.stalkMap Q.genericPoint).hom t ≠ 0 := fun t ht h0 => by
    have := ht.map (j.stalkMap x).hom
    rw [key, h0, map_zero] at this
    exact not_isUnit_zero this
  have hr0 := hne0 r hru
  have hs0 := hne0 s hsu
  -- the function-field identities on `T` and on `Y`
  set gT := (T.presheaf.stalkSpecializes
    (((genericPoint_spec T).specializes trivial : genericPoint T ⤳ x))).hom
  have e1 : algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom r) =
      gT ((j.stalkMap x).hom a₀) *
        algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom s) := by
    have hal : ∀ t, gT (T.presheaf.stalkSpecializes hspT t) = algebraMap _ T.functionField t :=
      fun t => algebraMap_stalkSpecializes hspT t
    have := congrArg (fun t => gT ((j.stalkMap x).hom t)) hrs'
    simp only [map_mul, key, hal] at this
    exact this.symm
  set gY := algebraMap (Y.presheaf.stalk (j x)) Y.functionField
  have e2 : algebraMap _ Y.functionField r =
      gY a₀ * algebraMap _ Y.functionField (s : Y.presheaf.stalk (j Q.genericPoint)) := by
    have := congrArg gY hrs'
    rw [map_mul] at this
    rw [← algebraMap_stalkSpecializes hspY, ← algebraMap_stalkSpecializes hspY]
    exact this.symm
  have e3 : ∀ W : irreducibleComponents Y,
      MMP.Threefold.Mori.Helpers.evalFF W (h : RationalFunctions Y) = gY a₀ := by
    intro W
    obtain rfl : W = pointComponent (j x) := irreducibleComponents_eq _ _
    change (Y.presheaf.stalkSpecializes _).hom ((h : RationalFunctions Y) _) = _
    rw [← ha₀spec]
    change (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.stalkSpecializes _).hom _) = _
    rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  have hgYa : gY a₀ ≠ 0 := (a₀.isUnit.map gY).ne_zero
  have hsne : (s : Y.presheaf.stalk (j Q.genericPoint)) ≠ 0 := fun h0 =>
    hs0 (by rw [h0, map_zero])
  have hsK : algebraMap _ Y.functionField (s : Y.presheaf.stalk (j Q.genericPoint)) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]; exact hsne
  have hordE : ∀ E : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ E.support →
      B.coeff E = Y.ord (algebraMap _ Y.functionField r) E.genericPoint -
        Y.ord (algebraMap _ Y.functionField (s : Y.presheaf.stalk (j Q.genericPoint)))
          E.genericPoint := by
    intro E hE
    rw [hh E ⟨_, hE, hyU⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, e3, e2,
      Scheme.ord_mul hgYa hsK]
    ring
  have hcK : gT ((j.stalkMap x).hom a₀) ≠ 0 := ((a₀.isUnit.map (j.stalkMap x).hom).map gT).ne_zero
  have hsT : algebraMap _ T.functionField
      ((j.stalkMap Q.genericPoint).hom (s : Y.presheaf.stalk (j Q.genericPoint))) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]; exact hs0
  rw [hD, hc, ordUnit_eq_ord, sum_intersectionLength_smul_eq_ord_sub sY j Q B r s hr0 hs0 hordE,
    e1, Scheme.ord_mul hcK hsT]
  exact add_sub_cancel_right _ _

/-- The pulled-back local equation `j^*_Z h` is the germ of `j^* b` for any section `b` of `𝒪_Y`
representing `h` on an open `V` whose preimage contains the generic point of `Z`. -/
private theorem pullbackComponent_eq_germ {Y T : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    (j : T ⟶ Y) {B : Divisor Y}
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ B.supp)
    {U : Y.Opens} {h : (RationalFunctions Y)ˣ} (hh : B.IsLocalEquation U h)
    (Z : irreducibleComponents T) (hZU : j (componentGenericPoint T Z) ∈ U) (V : Y.Opens)
    (b : Γ(Y, V)) (hrep : ∀ (W : irreducibleComponents Y) (hW : componentGenericPoint Y W ∈ V),
      (h : RationalFunctions Y) W = Y.presheaf.germ V _ hW b)
    (hZV : componentGenericPoint T Z ∈ j ⁻¹ᵁ V) :
    ((pullbackComponent j hB hh Z hZU : (T.presheaf.stalk _)ˣ) : T.presheaf.stalk _) =
      T.presheaf.germ (j ⁻¹ᵁ V) _ hZV (j.app V b) := by
  have hspec := (hh.exists_unit_stalk hZU (hB Z) (mem_pointComponent _)).choose_spec
  have hWV : componentGenericPoint Y (pointComponent (j (componentGenericPoint T Z))) ∈ V :=
    ((isGenericPoint_componentGenericPoint Y _).specializes (mem_pointComponent _)).mem_open
      V.isOpen hZV
  have heq : ((hh.exists_unit_stalk hZU (hB Z) (mem_pointComponent _)).choose :
      Y.presheaf.stalk _) = Y.presheaf.germ V _ hZV b := by
    apply stalkToRationalFunctions_injective (mem_pointComponent (j (componentGenericPoint T Z)))
    rw [hspec, hrep _ hWV]
    have := TopCat.Presheaf.germ_stalkSpecializes Y.presheaf (U := V) hZV
      ((isGenericPoint_componentGenericPoint Y _).specializes (mem_pointComponent _))
    exact (ConcreteCategory.congr_hom this b).symm
  change (j.stalkMap (componentGenericPoint T Z)).hom
    ((hh.exists_unit_stalk hZU (hB Z) (mem_pointComponent _)).choose :
      Y.presheaf.stalk (j (componentGenericPoint T Z))) = _
  rw [heq]
  exact Scheme.Hom.germ_stalkMap_apply j V _ hZV b

end Pullback

/-- **The restriction to a smooth prime divisor is the pull-back.** Let `sY : Y ⟶ Spec k` be a
smooth variety, `F` a prime divisor of `Y` whose subscheme `ι : F.idealSheaf.subscheme ⟶ Y` is
smooth over `k`, and `B` a divisor on `Y` with `B.coeff F = 0`. Then no generic point of `F` lies
on `B`, and the restriction `B|_F` is the pull-back `ι^* B`. -/
public theorem isPullback_restrictPrimeDivisor (k : Type u) [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [hY : IsSmoothVariety k sY] (F : PrimeDivisor Y)
    [hF : Smooth (F.idealSheaf.subschemeι ≫ sY)] (B : Divisor Y) (hBF : B.coeff F = 0) :
    letI : IsLocallyNoetherian Y :=
      @LocallyOfFiniteType.isLocallyNoetherian _ _ sY hY.toLocallyOfFiniteType
        (isLocallyNoetherian_Spec.mpr inferInstance)
    letI : IsNormal Y := @isNormal_of_smooth_over_field k _ Y sY hY.toSmooth
    letI : IsLocallyNoetherian F.idealSheaf.subscheme :=
      @LocallyOfFiniteType.isLocallyNoetherian _ _ (F.idealSheaf.subschemeι ≫ sY) inferInstance
        (isLocallyNoetherian_Spec.mpr inferInstance)
    letI : IsNormal F.idealSheaf.subscheme :=
      @isNormal_of_smooth_over_field k _ _ (F.idealSheaf.subschemeι ≫ sY) hF
    ∃ hB, B.IsPullback F.idealSheaf.subschemeι hB (B.restrictPrimeDivisor F) := by
  letI : IsLocallyNoetherian Y :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ sY hY.toLocallyOfFiniteType
      (isLocallyNoetherian_Spec.mpr inferInstance)
  letI : IsNormal Y := @isNormal_of_smooth_over_field k _ Y sY hY.toSmooth
  letI : IsLocallyNoetherian F.idealSheaf.subscheme :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (F.idealSheaf.subschemeι ≫ sY) inferInstance
      (isLocallyNoetherian_Spec.mpr inferInstance)
  letI : IsNormal F.idealSheaf.subscheme :=
    @isNormal_of_smooth_over_field k _ _ (F.idealSheaf.subschemeι ≫ sY) hF
  haveI : CompactSpace Y :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ sY hY.toQuasiCompact PrimeSpectrum.compactSpace
  haveI : IsNoetherian Y := ⟨⟩
  haveI : Smooth sY := hY.toSmooth
  haveI := F.integral
  refine ⟨fun Z hZ => ?_, isPullback_of_coeff_eq sY F.idealSheaf.subschemeι B _ _
    (DivisorWithCoeffs.coeff_restrictPrimeDivisor B F hBF)⟩
  change _ ∈ ((B.support.sup fun E => E.idealSheaf.support : Closeds Y) : Set Y) at hZ
  rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_eq_iSup] at hZ
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Function.comp_apply] at hZ
  obtain ⟨E, hE, hmem⟩ := hZ
  exact DivisorWithCoeffs.forall_notMem_support_primeDivisor B F hBF E hE _
    (coheight_componentGenericPoint Z) hmem

/-- **Restriction of a divisor to a smooth prime divisor.** Let `sY : Y ⟶ Spec k` be a smooth
variety, `F` a prime divisor of `Y` whose subscheme `ι : F.idealSheaf.subscheme ⟶ Y` is smooth
over `k`, and `B` a divisor on `Y` with `B.coeff F = 0`. Then `B|_F` is Cartier, the divisorial
sheaf `𝒪_F(B|_F)` is isomorphic to `ι^* 𝒪_Y(B)`, and whenever `h` is a local equation of `B` on
`U`, there is a restriction `φ` of `h` to `F` (agreeing with `ι^* a` for every section `a` of
`𝒪_Y` representing `h` on an open `V ⊆ U`), and every such restriction is a local equation of
`B|_F` on `ι⁻¹ U`. -/
@[mmp "lem_km3a_restriction_line_bundle"]
public theorem isCartier_restrictPrimeDivisor_of_isSmoothVariety (k : Type u) [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [hY : IsSmoothVariety k sY]
    (F : PrimeDivisor Y) [hF : Smooth (F.idealSheaf.subschemeι ≫ sY)]
    (B : Divisor Y) (hBF : B.coeff F = 0) :
    letI : IsLocallyNoetherian Y :=
      @LocallyOfFiniteType.isLocallyNoetherian _ _ sY hY.toLocallyOfFiniteType
        (isLocallyNoetherian_Spec.mpr inferInstance)
    letI : IsNormal Y := @isNormal_of_smooth_over_field k _ Y sY hY.toSmooth
    letI : IsLocallyNoetherian F.idealSheaf.subscheme :=
      @LocallyOfFiniteType.isLocallyNoetherian _ _ (F.idealSheaf.subschemeι ≫ sY) inferInstance
        (isLocallyNoetherian_Spec.mpr inferInstance)
    letI : IsNormal F.idealSheaf.subscheme :=
      @isNormal_of_smooth_over_field k _ _ (F.idealSheaf.subschemeι ≫ sY) hF
    IsCartier (B.restrictPrimeDivisor F) ∧
    Nonempty (divisorialSheaf (B.restrictPrimeDivisor F) ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj B.divisorialSheaf) ∧
    ∀ (U : Y.Opens) (h : (RationalFunctions Y)ˣ), B.IsLocalEquation U h →
      let IsRestriction : (RationalFunctions F.idealSheaf.subscheme)ˣ → Prop := fun φ =>
        ∀ (V : Y.Opens), V ≤ U → ∀ a : Γ(Y, V),
          (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ V),
            (h : RationalFunctions Y) Z = Y.presheaf.germ V _ hZ a) →
          ∀ (Z : irreducibleComponents F.idealSheaf.subscheme)
            (hZ : componentGenericPoint _ Z ∈ F.idealSheaf.subschemeι ⁻¹ᵁ V),
            (φ : RationalFunctions F.idealSheaf.subscheme) Z =
              F.idealSheaf.subscheme.presheaf.germ _ _ hZ (F.idealSheaf.subschemeι.app V a)
      (∃ φ, IsRestriction φ) ∧
        ∀ φ, IsRestriction φ →
          IsLocalEquation (B.restrictPrimeDivisor F) (F.idealSheaf.subschemeι ⁻¹ᵁ U) φ := by
  letI : IsLocallyNoetherian Y :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ sY hY.toLocallyOfFiniteType
      (isLocallyNoetherian_Spec.mpr inferInstance)
  letI : IsNormal Y := @isNormal_of_smooth_over_field k _ Y sY hY.toSmooth
  letI : IsLocallyNoetherian F.idealSheaf.subscheme :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (F.idealSheaf.subschemeι ≫ sY) inferInstance
      (isLocallyNoetherian_Spec.mpr inferInstance)
  letI : IsNormal F.idealSheaf.subscheme :=
    @isNormal_of_smooth_over_field k _ _ (F.idealSheaf.subschemeι ≫ sY) hF
  haveI : CompactSpace Y :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ sY hY.toQuasiCompact PrimeSpectrum.compactSpace
  haveI : IsNoetherian Y := ⟨⟩
  haveI : Smooth sY := hY.toSmooth
  haveI := F.integral
  haveI : CompactSpace F.idealSheaf.subscheme :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ (F.idealSheaf.subschemeι ≫ sY) inferInstance
      PrimeSpectrum.compactSpace
  set ι := F.idealSheaf.subschemeι
  obtain ⟨hB, hP⟩ := isPullback_restrictPrimeDivisor k sY F B hBF
  have hBc : B.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme ((MMP.Mori.isSmoothScheme_iff sY).2 inferInstance) B
  refine ⟨MMP.Fourfold.isCartier_of_isSmoothScheme
    ((MMP.Mori.isSmoothScheme_iff (ι ≫ sY)).2 inferInstance) _,
    ⟨hP.divisorialSheafIso (hBc := hBc)⟩, ?_⟩
  intro U h hh IsRestriction
  classical
  refine ⟨⟨(MMP.Mori.RationalFunctions.unitsEquiv _).symm fun Z =>
    if hZ : ι (componentGenericPoint _ Z) ∈ U then pullbackComponent ι hB hh Z hZ else 1, ?_⟩, ?_⟩
  · intro V hVU b hrep Z hZ
    have hZU : ι (componentGenericPoint _ Z) ∈ U := hVU hZ
    change (((if hZ' : ι (componentGenericPoint _ Z) ∈ U then pullbackComponent ι hB hh Z hZ'
      else 1 : (F.idealSheaf.subscheme.presheaf.stalk (componentGenericPoint _ Z))ˣ)) :
        F.idealSheaf.subscheme.presheaf.stalk (componentGenericPoint _ Z)) = _
    rw [dif_pos hZU]
    exact pullbackComponent_eq_germ ι hB hh Z hZU V b hrep hZ
  · intro φ hφ Q hQ
    rw [hP U h hh Q hQ, MMP.Mori.PrimeDivisor.ord_eq_ordUnit]
    congr 1
    set x := componentGenericPoint _ Q.component
    have hx : ι x ∈ U := Q.map_componentGenericPoint_mem ι hQ
    have hspec :=
      (hh.exists_unit_stalk hx (hB Q.component) (MMP.Mori.mem_pointComponent _)).choose_spec
    obtain ⟨V', hm, b, hb⟩ := TopCat.Presheaf.germ_exist Y.presheaf
      ((hh.exists_unit_stalk hx (hB Q.component) (MMP.Mori.mem_pointComponent _)).choose :
        Y.presheaf.stalk (ι x))
    let V := V' ⊓ U
    let b' := Y.presheaf.map (homOfLE (inf_le_left : V ≤ V')).op b
    have hrep : ∀ (W : irreducibleComponents Y) (hW : componentGenericPoint Y W ∈ V),
        (h : RationalFunctions Y) W = Y.presheaf.germ V _ hW b' := by
      intro W hW
      obtain rfl : W = MMP.Mori.pointComponent (ι x) := irreducibleComponents_eq _ _
      rw [← hspec, ← hb]
      have := TopCat.Presheaf.germ_stalkSpecializes Y.presheaf (U := V') hm
        ((MMP.Mori.isGenericPoint_componentGenericPoint Y _).specializes
          (MMP.Mori.mem_pointComponent _))
      refine (ConcreteCategory.congr_hom this b).trans ?_
      exact (Y.presheaf.germ_res_apply (homOfLE (inf_le_left : V ≤ V')) _ hW b).symm
    have hxV : x ∈ ι ⁻¹ᵁ V := ⟨hm, hx⟩
    apply Units.ext
    refine (pullbackComponent_eq_germ ι hB hh _ hx V b' hrep hxV).trans ?_
    exact (hφ V inf_le_right b' hrep Q.component hxV).symm

section Adjunction

open MonoidalCategory

variable {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- **Restriction to a prime divisor is surjective on sections when `H¹` vanishes.** On a smooth
variety, if `H¹(Y, 𝒪_Y(D)) = 0` then `H⁰(Y, 𝒪_Y(D + F)) ⟶ H⁰(F, i^* 𝒪_Y(D + F))` is surjective.
-/
public theorem surjective_cohomologyOverFieldMap_restriction (hV : IsVariety k f)
    (hsm : IsSmoothScheme f) (D : Divisor Y) (F : PrimeDivisor Y)
    (hH1 : Subsingleton (cohomologyOverField k f D.divisorialSheaf 1)) :
    Function.Surjective (cohomologyOverFieldMap k f
        ((Scheme.Modules.pullbackPushforwardAdjunction F.idealSheaf.subschemeι).unit.app
          (D + Finsupp.single F (1 : ℤ)).divisorialSheaf) 0 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k F.idealSheaf.subschemeι f
        ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj
          (D + Finsupp.single F (1 : ℤ)).divisorialSheaf) 0).inv).hom := by
  obtain ⟨_, hS⟩ := Divisor.IsCartier.shortExact_divisorialSheafInclusion_restriction f hV hsm F
    (MMP.Fourfold.isCartier_of_isSmoothScheme hsm D)
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  generalize cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k F.idealSheaf.subschemeι f
      ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj
        (D + Finsupp.single F (1 : ℤ)).divisorialSheaf) 0 = e
  rw [ModuleCat.hom_comp]
  exact e.toLinearEquiv.symm.surjective.comp fun y => (hgd 0 y).1 (Subsingleton.elim _ _)

/-- **Adjunction for a smooth prime divisor, twisted by a Cartier divisor.** On a smooth variety
`Y` of dimension `n + 1` with canonical divisor `K`, a prime divisor `F` smooth over `k` with
closed immersion `i` and a Cartier divisor `N`, `i^* 𝒪_Y(K + N + F) ≅ Ω^n_F ⊗ i^* 𝒪_Y(N)`. -/
public theorem nonempty_pullback_divisorialSheaf_iso_of_isCanonicalDivisor (hV : IsVariety k f)
    (hsm : IsSmoothScheme f) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor f (n + 1))
    (F : PrimeDivisor Y) (hF : IsSmoothScheme (F.idealSheaf.subschemeι ≫ f)) {N : Divisor Y}
    (hN : N.IsCartier) :
    Nonempty ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj
        (K + N + Finsupp.single F (1 : ℤ)).divisorialSheaf ≅
      Scheme.Hom.relativeDifferentialForms (F.idealSheaf.subschemeι ≫ f) n ⊗
        (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj N.divisorialSheaf) := by
  have hcart : ∀ D : Divisor Y, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  haveI : IsIntegral Y := hV.toIsIntegral
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsSmoothVariety k f := (isSmoothVariety_iff k f).2 ⟨hV, (isSmoothScheme_iff _).mp hsm⟩
  haveI : IsIntegral F.idealSheaf.subscheme := F.integral
  haveI : Smooth (F.idealSheaf.subschemeι ≫ f) := (isSmoothScheme_iff _).mp hF
  haveI : SmoothOfRelativeDimension (n + 1) f :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety f (n + 1) (by exact_mod_cast hK.1)
  obtain ⟨-, -, -, hiso, -, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k f
  obtain ⟨τ, hτe, hτs, hτW⟩ :=
    F.exists_isEffective_isSubschemeOfEffective_of_isSmoothVariety k f
  obtain ⟨⟨eAdj⟩, -⟩ := MMP.Intersection.nonempty_pullback_lineBundle_iso_of_smooth_divisor f
    (n := n) F.idealSheaf τ hτe hτs
  obtain ⟨eK⟩ := nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hsm hK
  obtain ⟨eτ⟩ : Nonempty (Divisor.divisorialSheaf (Finsupp.single F 1 : Divisor Y) ≅
      MMP.CartierDivisor.sheaf τ) := by
    rw [← hτW ⟨⟩]; exact hiso τ
  let i := F.idealSheaf.subschemeι
  let eKF : (K + Finsupp.single F 1).divisorialSheaf ≅
      Scheme.Hom.relativeDifferentialForms f ((n : ℤ) + 1) ⊗ MMP.CartierDivisor.sheaf τ :=
    ((hcart K).divisorialSheafTensorIso (hcart _)).symm ≪≫
      whiskerRightIso (eK ≪≫ eqToIso (by push_cast; rfl)) _ ≪≫ whiskerLeftIso _ eτ
  exact ⟨(Scheme.Modules.pullback i).mapIso
      (eqToIso (congrArg Divisor.divisorialSheaf (add_right_comm K N _)) ≪≫
        ((hcart _).divisorialSheafTensorIso hN).symm) ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorModulesIso i _ _ ≪≫
    whiskerRightIso ((Scheme.Modules.pullback i).mapIso eKF ≪≫ eAdj) _⟩

/-- **Restriction of adjoint sections to a smooth prime divisor** (Kollár–Mori 3.9). Let `Y` be a
smooth projective variety of dimension `n + 1` over `k` with canonical divisor `K`, `F` a smooth
prime divisor with closed immersion `i`, and `N` a Cartier divisor with `H¹(Y, 𝒪_Y(K + N)) = 0`.
Then the restriction `H⁰(Y, 𝒪_Y(K + N + F)) ⟶ H⁰(F, i^* 𝒪_Y(K + N + F))` is surjective, and
`i^* 𝒪_Y(K + N + F) ≅ Ωⁿ_{F/k} ⊗ i^* 𝒪_Y(N)`. -/
@[mmp "lem_km3a_restriction_surjective"]
public theorem surjective_restriction_of_subsingleton_cohomologyOverField_one
    (hY : IsProjectiveVariety k f) (hsm : IsSmoothScheme f) {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor f (n + 1)) (F : PrimeDivisor Y)
    (hF : IsSmoothScheme (F.idealSheaf.subschemeι ≫ f)) {N : Divisor Y} (hN : N.IsCartier)
    (hH1 : Subsingleton (cohomologyOverField k f (K + N).divisorialSheaf 1)) :
    Function.Surjective (cohomologyOverFieldMap k f
        ((Scheme.Modules.pullbackPushforwardAdjunction F.idealSheaf.subschemeι).unit.app
          (K + N + Finsupp.single F (1 : ℤ)).divisorialSheaf) 0 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k F.idealSheaf.subschemeι f
        ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj
          (K + N + Finsupp.single F (1 : ℤ)).divisorialSheaf) 0).inv).hom ∧
    Nonempty ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj
        (K + N + Finsupp.single F (1 : ℤ)).divisorialSheaf ≅
      Scheme.Hom.relativeDifferentialForms (F.idealSheaf.subschemeι ≫ f) n ⊗
        (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj N.divisorialSheaf) :=
  ⟨surjective_cohomologyOverFieldMap_restriction f hY.toIsVariety hsm _ F hH1,
    nonempty_pullback_divisorialSheaf_iso_of_isCanonicalDivisor f hY.toIsVariety hsm hK F hF hN⟩

end Adjunction

end Restriction

end MMP.Mori.Divisor

namespace MMP.Mori.DivisorWithCoeffs

section Restriction

open CategoryTheory AlgebraicGeometry

/-- In `Fin n` with `n ≤ 2`, two elements both different from a third are equal. -/
private lemma fin_eq_of_ne_of_ne {n : ℕ} (hn : n ≤ 2) {a b c : Fin n} (ha : a ≠ c)
    (hb : b ≠ c) : a = b := by
  rw [Ne, Fin.ext_iff] at ha hb
  ext
  omega

/-- If `F + ∑_{E ∈ S} E` is snc over any base, with `F ∉ S`, then along every prime divisor `Q`
of `F` the local intersection lengths of the `E ∈ S` sum to at most one: at the image `y` of the
generic point of `Q`, a regular system of parameters of `𝒪_{Y,y}` has at most two members, since
`𝒪_{F,Q} = 𝒪_{Y,y}/(z_F)` has dimension one, so at most one `E ∈ S` passes through `y`, and its
local equation generates the maximal ideal of `𝒪_{F,Q}`. -/
private lemma sum_intersectionLength_le_one {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (F : MMP.Mori.PrimeDivisor Y) (S : Finset (MMP.Mori.PrimeDivisor Y))
    (hF : F ∉ S)
    (hsnc : IsSNC f (Finsupp.single F (1 : ℤ) + ∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (Q : MMP.Mori.PrimeDivisor F.idealSheaf.subscheme) :
    ∑ E ∈ S, E.intersectionLength F.idealSheaf.subschemeι Q ≤ 1 := by
  classical
  set ι := F.idealSheaf.subschemeι
  set η := Q.genericPoint with hη
  set y := ι η
  set D : Divisor Y := Finsupp.single F (1 : ℤ) + ∑ E ∈ S, Finsupp.single E (1 : ℤ) with hD
  have hDapp : ∀ E, D E = (if E = F then 1 else 0) + (if E ∈ S then 1 else 0) := by
    intro E; simp [hD, Finsupp.finset_sum_apply, Finsupp.single_apply, eq_comm]
  have hFD : F ∈ D.support := by simp [hDapp, hF]
  have hSD : ∀ E ∈ S, E ∈ D.support := fun E hE => by
    simp [hDapp, hE, ne_of_mem_of_not_mem hE hF]
  have hyF : y ∈ F.support := by
    change y ∈ (F.idealSheaf.support : Set Y)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨η, rfl⟩
  obtain ⟨n, z, j, hz, hj, hI⟩ := hsnc.2 y
  set φ := (ι.stalkMap η).hom
  have hφs : Function.Surjective φ := ι.stalkMap_surjective η
  have hstalk : ∀ E (h : E ∈ D.support ∧ y ∈ E.support),
      E.idealSheaf.stalkIdeal y = Ideal.span {z (j ⟨E, h⟩)} := by
    intro E h
    rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk]
    exact hI ⟨E, h⟩
  have hker : RingHom.ker φ = Ideal.span {z (j ⟨F, hFD, hyF⟩)} :=
    (Scheme.IdealSheafData.ker_stalkMap_subschemeι F.idealSheaf η).trans
      (hstalk F ⟨hFD, hyF⟩)
  have hdimA : ringKrullDim (F.idealSheaf.subscheme.presheaf.stalk η) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hη,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; rfl
  have hmemB : ∀ i, z i ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := fun i =>
    hz.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hn : n ≤ 2 := by
    have h1 := Ideal.height_le_ringKrullDim_quotient_add_one
      (p := IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (hmemB (j ⟨F, hFD, hyF⟩))
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hz.2, ← hker,
      ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφs), hdimA,
      one_add_one_eq_two] at h1
    exact_mod_cast h1
  -- the components of `S` through `y` have pairwise distinct indices, distinct from `F`'s
  have hjne : ∀ E (h : E ∈ D.support ∧ y ∈ E.support), E ≠ F →
      j ⟨E, h⟩ ≠ j ⟨F, hFD, hyF⟩ := fun _ _ hEF hjj => hEF (congrArg Subtype.val (hj hjj))
  have hlen : ∀ E ∈ S, y ∈ E.support → E.intersectionLength ι Q ≤ 1 := by
    intro E hE hyE
    have hEF : E ≠ F := ne_of_mem_of_not_mem hE hF
    set i0 := j ⟨E, hSD E hE, hyE⟩
    set iF := j ⟨F, hFD, hyF⟩
    have hi : i0 ≠ iF := hjne E _ hEF
    have hmax : (E.idealSheaf.stalkIdeal (ι η)).map φ =
        IsLocalRing.maximalIdeal (F.idealSheaf.subscheme.presheaf.stalk η) := by
      rw [hstalk E ⟨hSD E hE, hyE⟩, Ideal.map_span, Set.image_singleton]
      apply le_antisymm
      · rw [Ideal.span_le, Set.singleton_subset_iff, ←
          IsLocalRing.map_maximalIdeal_of_surjective φ hφs]
        exact Ideal.mem_map_of_mem _ (hmemB i0)
      · rw [← IsLocalRing.map_maximalIdeal_of_surjective φ hφs, ← hz.1, Ideal.map_span,
          Ideal.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        by_cases hiF : i = iF
        · have : z i ∈ RingHom.ker φ := hker ▸ hiF ▸ Ideal.mem_span_singleton_self _
          rw [RingHom.mem_ker.mp this]
          exact Ideal.zero_mem _
        · rw [fin_eq_of_ne_of_ne hn hiF hi]
          exact Ideal.mem_span_singleton_self _
    have h1 : Module.length (F.idealSheaf.subscheme.presheaf.stalk η)
        ((F.idealSheaf.subscheme.presheaf.stalk η) ⧸
          (E.idealSheaf.stalkIdeal (ι η)).map φ) = 1 := by
      rw [Module.length_eq_one_iff, hmax, isSimpleModule_iff_isCoatom]
      exact (IsLocalRing.maximalIdeal.isMaximal _).out
    unfold PrimeDivisor.intersectionLength
    rw [h1]
    rfl
  have hzero : ∀ E ∈ S, y ∉ E.support → E.intersectionLength ι Q = 0 := fun E _ h =>
    PrimeDivisor.intersectionLength_eq_zero_of_notMem ι E h
  have hcard : (S.filter fun E => y ∈ E.support).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact congrArg Subtype.val (hj (fin_eq_of_ne_of_ne hn
      (hjne a ⟨hSD a ha.1, ha.2⟩ (ne_of_mem_of_not_mem ha.1 hF))
      (hjne b ⟨hSD b hb.1, hb.2⟩ (ne_of_mem_of_not_mem hb.1 hF))))
  calc ∑ E ∈ S, E.intersectionLength ι Q
      = ∑ E ∈ S.filter fun E => y ∈ E.support, E.intersectionLength ι Q := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun E hE => ?_
        split_ifs with h
        · rfl
        · exact hzero E hE h
    _ ≤ (S.filter fun E => y ∈ E.support).card • 1 :=
        Finset.sum_le_card_nsmul _ _ _ fun E hE => by
          rw [Finset.mem_filter] at hE; exact hlen E hE.1 hE.2
    _ ≤ 1 := by simpa using hcard

/-- In a domain, a nonzero prime contained in a prime of height one is equal to it. -/
private lemma eq_of_le_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A] {I q : Ideal A}
    [I.IsPrime] [q.IsPrime] (hI : I ≠ ⊥) (hle : I ≤ q) (hq : q.height = 1) : I = q := by
  by_contra hne
  have : q.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hq]; simp))
  have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hq, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
  exact hI h1

/-- Let `J` be an ideal sheaf contained in the ideal of a prime divisor `P`, and `y ∈ P` a point
at which `J` is cut out by a member of a regular system of parameters. Then `P` and `J` have the
same ideal at `y`: the generated ideal is a nonzero prime inside the height-one prime of `P`. -/
private lemma stalk_idealSheaf_eq_of_le {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : MMP.Mori.PrimeDivisor X) {J : X.IdealSheafData} (hle : J ≤ P.idealSheaf) {y : X}
    (hy : y ∈ P.support) {m : ℕ} {w : Fin m → X.presheaf.stalk y}
    (hw : IsRegularSystemOfParameters w) (j0 : Fin m)
    (hst : AlgebraicGeometry.IdealSheafData.stalk J y = Ideal.span {w j0}) :
    AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf y =
      AlgebraicGeometry.IdealSheafData.stalk J y := by
  obtain ⟨q, -, hPq, hq1⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hy
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk y)
  have := MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hw j0
  rw [hPq, hst]
  refine (eq_of_le_of_height_eq_one ?_ ?_ hq1).symm
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hw j0
  · rw [← hst, ← hPq]
    exact MMP.Resolution.stalk_le_stalk_of_le hle y

/-- Let `Y` be a smooth variety over an algebraically closed field `k` of characteristic
zero and `F` a prime divisor on `Y` not in the finite set `D` of prime divisors, such that
`F + ∑_{E ∈ D} E` is a simple normal crossing divisor. Then the restriction `(∑_{E ∈ D} E)|_F`
is a simple normal crossing divisor on `F`, all of whose nonzero coefficients equal `1`. -/
@[mmp "lem_km3a_snc_restriction"]
public theorem isSNC_restrictPrimeDivisor_sum_single {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsVariety k sY] [Smooth sY] (F : PrimeDivisor Y)
    (D : Finset (PrimeDivisor Y)) (hF : F ∉ D)
    (hsnc : IsSNC sY (Finsupp.single F (1 : ℤ) + ∑ E ∈ D, Finsupp.single E (1 : ℤ))) :
    IsSNC (F.idealSheaf.subschemeι ≫ sY)
        (restrictPrimeDivisor (∑ E ∈ D, Finsupp.single E (1 : ℤ)) F) ∧
      ∀ P ∈ (restrictPrimeDivisor (∑ E ∈ D, Finsupp.single E (1 : ℤ)) F).support,
        coeff (restrictPrimeDivisor (∑ E ∈ D, Finsupp.single E (1 : ℤ)) F) P = 1 := by
  classical
  obtain ⟨_, _, _, _⟩ := (isVariety_iff k sY).mp ‹_›
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  set ι := F.idealSheaf.subschemeι
  set T : Divisor Y := ∑ E ∈ D, Finsupp.single E (1 : ℤ) with hT
  have hTapp : ∀ E, T E = if E ∈ D then 1 else 0 := by
    intro E
    simp [hT, Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hTF : T.coeff F = 0 := by
    change T F = 0
    rw [hTapp, if_neg hF]
  have hTsupp : T.support ⊆ D := by
    intro E hE
    rw [Finsupp.mem_support_iff, hTapp] at hE
    by_contra h
    exact hE (if_neg h)
  -- the coefficients of `T|_F` are sums of local intersection lengths
  have hcoeff : ∀ Q, (restrictPrimeDivisor T F).coeff Q =
      ∑ E ∈ D, (E.intersectionLength ι Q : ℤ) := by
    intro Q
    rw [coeff_restrictPrimeDivisor _ F hTF Q,
      Finsupp.sum_of_support_subset _ hTsupp _ (fun _ _ => smul_zero _)]
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [hTapp, if_pos hE, nsmul_eq_mul, mul_one]
  -- every prime divisor of `F` in the support of `T|_F` lies in some `E ∈ D`
  have hexE : ∀ P ∈ (restrictPrimeDivisor T F).support, ∃ E ∈ D, ι P.genericPoint ∈ E.support := by
    intro P hP
    have hP' : (restrictPrimeDivisor T F).coeff P ≠ 0 := Finsupp.mem_support_iff.mp hP
    rw [hcoeff] at hP'
    obtain ⟨E, hE, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP'
    refine ⟨E, hE, ?_⟩
    by_contra h
    exact hne (by rw [PrimeDivisor.intersectionLength_eq_zero_of_notMem ι E h]; rfl)
  refine ⟨?_, fun P hP => ?_⟩
  swap
  · have hle : ∑ E ∈ D, E.intersectionLength ι P ≤ 1 :=
      sum_intersectionLength_le_one sY F D hF hsnc P
    have hP' : (restrictPrimeDivisor T F).coeff P ≠ 0 := Finsupp.mem_support_iff.mp hP
    rw [hcoeff, ← Nat.cast_sum] at hP' ⊢
    have h0 : ∑ E ∈ D, E.intersectionLength ι P ≠ 0 := by exact_mod_cast hP'
    have h1 : ∑ E ∈ D, E.intersectionLength ι P = 1 := by omega
    rw [h1, Nat.cast_one]
  -- local coordinates on `F` adapted to the `E ∩ F`, `E ∈ D`
  have hDapp : ∀ E, (Finsupp.single F (1 : ℤ) + T) E =
      (if E = F then 1 else 0) + (if E ∈ D then 1 else 0) := by
    intro E; rw [Finsupp.add_apply, hTapp, Finsupp.single_apply]; simp [eq_comm]
  have hFD : F ∈ (Finsupp.single F (1 : ℤ) + T).support := by
    rw [Finsupp.mem_support_iff, hDapp, if_pos rfl, if_neg hF]; exact one_ne_zero
  have hSD : ∀ E ∈ D, E ∈ (Finsupp.single F (1 : ℤ) + T).support := by
    intro E hE
    rw [Finsupp.mem_support_iff, hDapp, if_pos hE, if_neg (fun h : E = F => hF (h ▸ hE))]
    exact one_ne_zero
  let Efam : D → Y.IdealSheafData := fun E => E.1.idealSheaf
  have hZ : MMP.Resolution.HasSNCWith Efam F.idealSheaf := by
    intro x hx
    obtain ⟨n, z, j, hz, hj, hI⟩ := hsnc.2 x
    have hxF : x ∈ F.support := hx
    let c : {i // x ∈ (Efam i).support} → Fin n := fun i => j ⟨i.1.1, hSD i.1.1 i.1.2, i.2⟩
    refine ⟨n, z, c, {j ⟨F, hFD, hxF⟩}, hz, fun i => hI ⟨i.1.1, hSD i.1.1 i.1.2, i.2⟩,
      fun a b hab => ?_, ?_⟩
    · have := congrArg Subtype.val (hj hab)
      exact Subtype.ext (Subtype.ext this)
    · rw [hI ⟨F, hFD, hxF⟩]
      simp
  have hcomp : ∀ i, ∀ W ∈ MMP.Resolution.componentsOf (F.idealSheaf.support : Set Y),
      ¬ W ⊆ (Efam i).support := by
    intro i W hW hWE
    have hcl : (F.idealSheaf.support : Set Y) = closure {F.genericPoint} :=
      AlgebraicGeometry.PrimeDivisor.support_eq_closure F
    have hirr : IsIrreducible (F.idealSheaf.support : Set Y) := by
      rw [hcl]; exact isIrreducible_singleton.closure
    have hW' : Maximal (fun W' : Set Y => IsIrreducible W' ∧ W' ⊆ F.idealSheaf.support) W := hW
    have hWF : W = F.idealSheaf.support := (hW'.eq_of_ge ⟨hirr, le_rfl⟩ hW'.prop.2).symm
    have hmem : F.genericPoint ∈ i.1.support :=
      hWE (by rw [hWF, hcl]; exact subset_closure rfl)
    have hEF := i.1.eq_genericPoint_of_mem_support hmem F.coheight_genericPoint
    have : F = i.1 := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hEF
    exact hF (this ▸ i.2)
  have hcoord := MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith hZ hcomp
  have : IsLocallyNoetherian F.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sY)
  have hDc : ∀ i, ∀ y ∈ ((Efam i).comap ι).support, ∃ (m : ℕ)
      (w : Fin m → F.idealSheaf.subscheme.presheaf.stalk y) (j : Fin m),
        IsRegularSystemOfParameters w ∧
        AlgebraicGeometry.IdealSheafData.stalk ((Efam i).comap ι) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨n, z, c, hz, hc, -⟩ := hcoord y
    exact ⟨n, z, c ⟨i, hy⟩, hz, hc ⟨i, hy⟩⟩
  -- a prime divisor of `F` inside `E ∩ F` has the ideal of `E ∩ F` at each of its points
  have hmemc : ∀ (P : MMP.Mori.PrimeDivisor F.idealSheaf.subscheme) (i : D),
      ι P.genericPoint ∈ i.1.support → ∀ y ∈ P.support, y ∈ ((Efam i).comap ι).support := by
    intro P i hPi y hy
    have hsp : P.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hy
    exact hsp.mem_closed ((Efam i).comap ι).support.isClosed
      ((MMP.Resolution.mem_support_comap_iff _ _ _).2 hPi)
  have hkey : ∀ (P : MMP.Mori.PrimeDivisor F.idealSheaf.subscheme) (i : D),
      ι P.genericPoint ∈ i.1.support → ∀ y ∈ P.support,
        AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf y =
          AlgebraicGeometry.IdealSheafData.stalk ((Efam i).comap ι) y := by
    intro P i hPi y hy
    obtain ⟨m, w, j0, hw, hst⟩ := hDc i y (hmemc P i hPi y hy)
    refine stalk_idealSheaf_eq_of_le P ?_ hy hw j0 hst
    rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf P]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp fun x hx => hmemc P i hPi x hx
  choose E hED hEP using hexE
  refine ⟨fun P hP => ?_, fun y => ?_⟩
  · refine MMP.Resolution.isSmoothScheme_subscheme_of_stalk_eq_span_parameter (ι ≫ sY)
      P.idealSheaf fun y hy => ?_
    rw [hkey P ⟨E P hP, hED P hP⟩ (hEP P hP) y hy]
    exact hDc _ y (hmemc P _ (hEP P hP) y hy)
  · obtain ⟨m, w, c', hw, hc', hinj⟩ := hcoord y
    refine ⟨m, w, fun P => c' ⟨⟨E P.1 P.2.1, hED _ _⟩, hmemc P.1 _ (hEP _ _) y P.2.2⟩, hw,
      fun P P' h => ?_, fun P => ?_⟩
    · refine Subtype.ext (MMP.Intersection.eq_of_stalk_idealSheaf_eq P.2.2 P'.2.2 ?_)
      rw [hkey P.1 ⟨E P.1 P.2.1, hED _ P.2.1⟩ (hEP P.1 P.2.1) y P.2.2,
        hkey P'.1 ⟨E P'.1 P'.2.1, hED _ P'.2.1⟩ (hEP P'.1 P'.2.1) y P'.2.2]
      exact congrArg (fun i => AlgebraicGeometry.IdealSheafData.stalk ((Efam i).comap ι) y)
        (congrArg Subtype.val (hinj h))
    · rw [hkey P.1 ⟨E P.1 P.2.1, hED _ P.2.1⟩ (hEP P.1 P.2.1) y P.2.2]
      exact hc' ⟨⟨E P.1 P.2.1, hED _ P.2.1⟩, hmemc P.1 _ (hEP P.1 P.2.1) y P.2.2⟩

/-- Round-up commutes with a combination `∑ fᵢ bᵢ` whose natural coefficients sum to at most
one. -/
private lemma ceil_sum_nsmul {ι R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
    [FloorRing R] (s : Finset ι) (f : ι → ℕ) (b : ι → R) (hf : ∑ i ∈ s, f i ≤ 1) :
    ⌈∑ i ∈ s, f i • b i⌉ = ∑ i ∈ s, f i • ⌈b i⌉ := by
  classical
  by_cases h : ∃ i ∈ s, f i ≠ 0
  · obtain ⟨i, hi, hfi⟩ := h
    have hother : ∀ j ∈ s, j ≠ i → f j = 0 := by
      intro j hj hji
      have := Finset.add_le_sum (f := f) (fun _ _ => Nat.zero_le _) hi hj (Ne.symm hji)
      omega
    have hfi1 : f i = 1 := by
      have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hi
      omega
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => by rw [hother j hj hji, zero_smul]),
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => by rw [hother j hj hji, zero_smul]),
      hfi1, one_smul, one_smul]
  · push Not at h
    rw [Finset.sum_eq_zero (f := fun i => f i • b i) (fun i hi => by simp [h i hi]),
      Finset.sum_eq_zero (f := fun i => f i • ⌈b i⌉) (fun i hi => by simp [h i hi]),
      Int.ceil_zero]

/-- **Round-up commutes with restriction** (Kollár–Mori 3.10). On a smooth variety `Y`, let `F`
be a smooth prime divisor, `L` a Cartier divisor whose support does not contain `F`, and `B` a
divisor with coefficients in `R` of which `F` is not a component and such that `F + B` is snc.
Then for `D = L + B` the round-up of the restriction of `D` to `F` is the restriction of the
round-up `⌈D⌉`: `⌈D⌉|_F = ⌈D|_F⌉`. -/
@[mmp "lem_km3a_roundup_commutes_restriction"]
public theorem restrictPrimeDivisor_roundUp {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k))
    {R : Type v} [Ring R] [LinearOrder R] [IsOrderedRing R] [FloorRing R]
    (hY : IsVariety k sY) (hYsm : IsSmoothScheme sY)
    (F : PrimeDivisor Y) (hF : IsSmoothScheme (F.idealSheaf.subschemeι ≫ sY))
    (L : Divisor Y) (hL : L.IsCartier) (hLF : ¬ (F.support : Set Y) ⊆ supp L)
    (B : DivisorWithCoeffs R Y) (hBF : B.coeff F = 0)
    (hsnc : IsSNC sY (Finsupp.single F (1 : R) + B)) :
    restrictPrimeDivisor (roundUp (ofDivisor R L + B)) F =
      roundUp (restrictPrimeDivisor (ofDivisor R L + B) F) := by
  classical
  obtain ⟨_, _, _, _⟩ := (isVariety_iff k sY).mp hY
  have : Smooth sY := (isSmoothScheme_iff sY).mp hYsm
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  have hLF0 : L.coeff F = 0 := by
    by_contra h
    exact hLF (support_subset_supp h)
  set S := B.support with hS
  have hFS : F ∉ S := by rw [hS, Finsupp.notMem_support_iff]; exact hBF
  set T : Divisor Y := ∑ E ∈ S, Finsupp.single E (1 : ℤ) with hTdef
  have hT : ∀ E, T E = if E ∈ S then 1 else 0 := by
    intro E
    simp [hTdef, Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hsncT : IsSNC sY (Finsupp.single F (1 : ℤ) + T) := by
    refine hsnc.of_support_subset fun E hE => ?_
    by_cases hEF : E = F
    · subst hEF; simp [show B E = 0 from hBF]
    · simp_all [Finsupp.single_apply, Ne.symm hEF, hS]
  have hsum : ∀ Q : MMP.Mori.PrimeDivisor F.idealSheaf.subscheme,
      ∑ E ∈ S, E.intersectionLength F.idealSheaf.subschemeι Q ≤ 1 :=
    sum_intersectionLength_le_one sY F S hFS hsncT
  set U := L.support ∪ S with hU
  have hDF : (ofDivisor R L + B).coeff F = 0 := by simp [hLF0, hBF]
  have hl : ∀ E, (roundUp (ofDivisor R L + B)) E = L E + ⌈B E⌉ := by
    intro E
    change (roundUp (ofDivisor R L + B)).coeff E = _
    rw [coeff_roundUp, coeff_add, coeff_ofDivisor, add_comm, Int.ceil_add_intCast, add_comm]
    rfl
  have hr : ∀ E, (ofDivisor R L + B) E = (L E : R) + B E := fun E => rfl
  have hDU : (ofDivisor R L + B).support ⊆ U := fun E hE => by
    contrapose! hE
    simp_all [hU, hr]
  have hRU : (roundUp (ofDivisor R L + B)).support ⊆ U := fun E hE => by
    contrapose! hE
    simp_all [hU, hl]
  ext Q
  change (restrictPrimeDivisor (roundUp (ofDivisor R L + B)) F).coeff Q =
    (roundUp (restrictPrimeDivisor (ofDivisor R L + B) F)).coeff Q
  rw [coeff_roundUp, coeff_restrictPrimeDivisor _ F (by rw [coeff_roundUp, hDF, Int.ceil_zero]) Q,
    coeff_restrictPrimeDivisor _ F hDF Q,
    Finsupp.sum_of_support_subset _ hRU _ (fun _ _ => smul_zero _),
    Finsupp.sum_of_support_subset _ hDU _ (fun _ _ => smul_zero _)]
  set len := fun E : MMP.Mori.PrimeDivisor Y => E.intersectionLength F.idealSheaf.subschemeι Q
  have hBU : ∑ E ∈ U, len E • B E = ∑ E ∈ S, len E • B E :=
    (Finset.sum_subset Finset.subset_union_right fun E _ hE => by simp_all [hS]).symm
  have hBU' : ∑ E ∈ U, len E • ⌈B E⌉ = ∑ E ∈ S, len E • ⌈B E⌉ :=
    (Finset.sum_subset Finset.subset_union_right fun E _ hE => by simp_all [hS]).symm
  have hcast : ∑ E ∈ U, len E • (L E : R) = ((∑ E ∈ U, len E • L E : ℤ) : R) := by
    simp [Int.cast_sum, nsmul_eq_mul]
  change ∑ E ∈ U, len E • (roundUp (ofDivisor R L + B)) E =
    ⌈∑ E ∈ U, len E • (ofDivisor R L + B) E⌉
  simp only [hl, hr, smul_add, Finset.sum_add_distrib]
  rw [hcast, Int.ceil_intCast_add, hBU, hBU', ceil_sum_nsmul S len _ (hsum Q)]

end Restriction

end MMP.Mori.DivisorWithCoeffs

namespace MMP.Threefold.Resolution

section BlowupPoint

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Resolution

/-- If the order of the ideal `(φ)` is finite, it is the order of `φ`. -/
private theorem maximalIdealOrder_eq_of_idealOrder_span_eq {R : Type*} [CommRing R]
    [IsLocalRing R] {φ : R} {n : ℕ} (h : idealOrder (Ideal.span {φ}) = n) :
    MMP.Flips.maximalIdealOrder R φ = n := by
  set S := {j : ℕ | φ ∈ IsLocalRing.maximalIdeal R ^ j}
  have key : idealOrder (Ideal.span {φ}) = ⨆ j ∈ S, (j : ℕ∞) := by
    simp only [idealOrder, Ideal.span_singleton_le_iff_mem, S, Set.mem_setOf_eq]
  have hbdd : BddAbove S := ⟨n, fun j hj => by
    exact_mod_cast h ▸ key ▸ le_iSup₂ (f := fun j (_ : j ∈ S) => (j : ℕ∞)) j hj⟩
  have := ENat.coe_sSup hbdd
  rw [← key, h] at this
  exact_mod_cast this

/-- The generic point of the reduced closed point `{y}` is `y`. -/
private theorem genericPoint_support_vanishingIdeal_singleton {Y : Scheme.{u}} {y : Y}
    (hy : IsClosed ({y} : Set Y)) :
    (isIrreducible_support_vanishingIdeal_singleton hy).genericPoint = y := by
  have h := (isIrreducible_support_vanishingIdeal_singleton hy).isGenericPoint_genericPoint_closure
  rw [show closure ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support :
      Set Y) = closure {y} by rw [support_vanishingIdeal_singleton hy]] at h
  exact h.eq isGenericPoint_closure

/-- A closed point of an irreducible scheme of positive dimension has codimension `≥ 1`. -/
private theorem one_le_codimension_singleton {Y : Scheme.{u}} [IrreducibleSpace Y] {d : ℕ}
    (hYd : topologicalKrullDim Y = d) (hd : 1 ≤ d) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    1 ≤ codimension (⟨(Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support,
      isIrreducible_support_vanishingIdeal_singleton hy,
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support.isClosed⟩ :
        IrreducibleCloseds Y) := by
  rw [codimension_eq_coheight, Order.one_le_iff_ne_zero, Order.coheight_ne_zero]
  intro hmax
  have huniv : (Set.univ : Set Y) ⊆ {y} := fun a _ => by
    have : a ∈ ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support :
        Set Y) := hmax (b := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩)
      (fun _ _ => trivial) (Set.mem_univ a)
    rwa [support_vanishingIdeal_singleton hy] at this
  have : Subsingleton Y := ⟨fun a b => (huniv trivial).trans (huniv trivial).symm⟩
  have : DiscreteTopology Y := Subsingleton.discreteTopology
  have h0 := topologicalKrullDim_zero_of_discreteTopology Y
  rw [hYd] at h0
  have : d ≤ 0 := by exact_mod_cast h0
  omega

/-- **The exceptional coefficient of a pulled-back prime divisor is its local order.** Let `X` be
a variety of dimension `d ≥ 2` smooth over an algebraically closed field `k`, `x ∈ X` a closed
point, `π : B_x X ⟶ X` the blow-up of `x` and `E` the prime divisor of `B_x X` with ideal sheaf
`exceptionalIdeal`. If `P` is a prime divisor of `X` and `h ∈ 𝒪_{X,x}` generates the stalk at `x`
of the ideal sheaf of `P`, then the coefficient of `E` in the pull-back `π^*P` is
`MMP.Flips.maximalIdealOrder 𝒪_{X,x} h`. -/
@[mmp "lem_mmp_foundation_blowup_point_order_multiplicity"]
public theorem coeff_exceptional_eq_maximalIdealOrder_of_isPullback
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : Mori.IsVariety k sX) [Smooth sX] {d : ℕ} (hd : topologicalKrullDim X = d)
    (hd2 : 2 ≤ d) {x : X} (hx : IsClosed ({x} : Set X)) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsNormal X := isNormal_of_smooth_over_field sX
    haveI : Smooth (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ≫ sX) :=
      (isVariety_smooth_blowUpToBase_vanishingIdeal_singleton sX hX hd hd2 hx).2.1
    haveI : IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ≫ sX)
    haveI : IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) :=
      isNormal_of_smooth_over_field
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ≫ sX)
    ∀ (E : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)))
      (hE : E.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩))
      (P : Mori.PrimeDivisor X) (h : X.presheaf.stalk x)
      (hh : IdealSheafData.stalk P.idealSheaf x = Ideal.span {h})
      (hB : ∀ Z : irreducibleComponents (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)),
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) (Mori.componentGenericPoint _ Z) ∉
          Mori.DivisorWithCoeffs.supp (Finsupp.single P (1 : ℤ) : Mori.Divisor X))
      (B' : Mori.Divisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)))
      (hB' : Mori.Divisor.IsPullback
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩))
        (Finsupp.single P (1 : ℤ) : Mori.Divisor X) hB B'),
      B'.coeff E = (Flips.maximalIdealOrder (X.presheaf.stalk x) h : ℤ) := by
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsIntegral X := hX.toIsIntegral
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsNormal X := isNormal_of_smooth_over_field sX
  haveI : Smooth (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ≫ sX) :=
    (isVariety_smooth_blowUpToBase_vanishingIdeal_singleton sX hX hd hd2 hx).2.1
  haveI : IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ≫ sX)
  haveI : IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) :=
    isNormal_of_smooth_over_field
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ≫ sX)
  intro E hE P h hh hB B' hB'
  have hXs : MMP.Mori.IsSmoothScheme sX := MMP.Resolution.isSmoothScheme_of_smooth sX
  have hPe := isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hXs P
  have hsb := isSmoothBlowup_vanishingIdeal_singleton sX hXs hx
  have hirr := isIrreducible_support_vanishingIdeal_singleton hx
  have hcodim := one_le_codimension_singleton hd (by omega) hx
  obtain ⟨n, hn, hcoef⟩ := coeff_isPullback_single_eq_idealOrder P hPe hB' E
  rw [hcoef]
  have hord := orderAlong_comap_blowUpToBase_eq sX _ hsb hirr hcodim P.idealSheaf
  have hE' : exceptionalPrimeDivisor sX _ hsb hirr hcodim = E :=
    MMP.Mori.PrimeDivisor.ext_idealSheaf (by rw [hE]; rfl)
  simp only [orderAlong, multAt] at hord
  rw [isIrreducible_genericPoint_eq _ (isIrreducible_support_exceptionalPrimeDivisor sX _ hsb
    hirr hcodim)] at hord
  rw [genericPoint_support_vanishingIdeal_singleton hx, hE', hn, hh] at hord
  rw [maximalIdealOrder_eq_of_idealOrder_span_eq hord.symm]

end BlowupPoint

end MMP.Threefold.Resolution
