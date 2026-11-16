module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.MMP.Fourfold.RestrictedSeries
public import MMP.AlgebraicGeometry.MMP.Fourfold.AlgebraicLemmas
public import MMP.AlgebraicGeometry.MMP.Fourfold.ExceptionalSupport
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity

/-!
# Stable base primes of a good birational model, and monotone fixed parts

## Main results

* `MMP.Fourfold.isInRelativeDivisorialStableBase_iff_pos_transformDivisor`: let `p : T ⟶ X` and
  `q : T ⟶ Y` be proper birational morphisms of normal varieties over `Z` and `D, D'` real
  Cartier divisors with `p^*D = q^*D' + E`, `E ≥ 0`, `q_*E = 0`. If `D'` is real linearly
  equivalent over `Z` to a nonnegative real combination of relatively free integral Cartier
  divisors, then the prime divisors of the relative divisorial stable base locus of `D` are exactly
  the primes with positive coefficient in `p_*E`.
* `MMP.Fourfold.restrictedNormalizedFixedPart_factorial_succ_le`,
  `MMP.Fourfold.tendsto_restrictedNormalizedFixedPart_factorial`,
  `MMP.Fourfold.restrictedAsymptoticFixedPart_ne_top`,
  `MMP.Fourfold.finite_support_restrictedAsymptoticFixedPart`,
  `MMP.Fourfold.restrictedAsymptoticFixedPart_le_normalizedFixedPart`: for a graded restricted
  series, the factorial fixed parts `F_{q n!}` decrease to `F`, a finite-support effective real
  divisor, and every admissible `F_m` is at least `F`.
* `MMP.Fourfold.restrictedClippedBoundaryAt_factorial_le_succ`,
  `MMP.Fourfold.tendsto_restrictedClippedBoundaryAt_factorial`,
  `MMP.Fourfold.support_restrictedClippedBoundaryAt_subset`,
  `MMP.Fourfold.exists_isKltPair_restrictedClippedBoundaryAt`: the boundaries `Θ_{q n!}` increase
  to `Θ`, are supported on `Supp Θ`, and are rational klt.
* `MMP.Fourfold.not_isInRelativeDivisorialStableBase_restrictedClippedBoundaryAt`: no component of
  `Θ_m` is a stable base prime of `K_S + Θ_m`.

## Implementation notes

`ℝ`-linear equivalence over `Z` is the one in the definition of the relative divisorial stable base
locus: `D' = ∑ cᵢ Hᵢ + ∑ bⱼ div hⱼ` with `hⱼ ∈ K(Y)^×`. The pull-backs of `D, D'` are given by
the predicate `MMP.Flips.IsRCartierPullback` (unique by `MMP.Flips.IsRCartierPullback.eq`), so
`p^*D = q^*D' + E` is stated as `GD = GD' + E` for pull-backs `GD`, `GD'`. The boundaries `Θ_m`
being rational klt uses that `S` is smooth, so that every `ℚ`-divisor is `ℚ`-Cartier and
discrepancies decrease on adding an effective divisor.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

set_option linter.unusedSectionVars false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

section RPullbackAlgebra

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- The zero `ℝ`-divisor on `Y` is an `ℝ`-Cartier pullback of the zero `ℝ`-divisor on `X`. -/
theorem isRCartierPullback_zero (f : Y ⟶ X) : MMP.Flips.IsRCartierPullback f 0 0 :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩

/-- If `G₁` and `G₂` are `ℝ`-Cartier pullbacks of `D₁` and `D₂` along `f`, then `G₁ + G₂` is an
`ℝ`-Cartier pullback of `D₁ + D₂`. -/
theorem isRCartierPullback_add {f : Y ⟶ X} {D₁ D₂ : RDivisor X} {G₁ G₂ : RDivisor Y}
    (h₁ : MMP.Flips.IsRCartierPullback f D₁ G₁) (h₂ : MMP.Flips.IsRCartierPullback f D₂ G₂) :
    MMP.Flips.IsRCartierPullback f (D₁ + D₂) (G₁ + G₂) := by
  obtain ⟨m₁, r₁, L₁, L₁', hc₁, rfl, hp₁, rfl⟩ := h₁
  obtain ⟨m₂, r₂, L₂, L₂', hc₂, rfl, hp₂, rfl⟩ := h₂
  refine ⟨m₁ + m₂, Fin.append r₁ r₂, Fin.append L₁ L₂, Fin.append L₁' L₂', ?_, ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hc₁ i
    · simpa using hc₂ i
  · rw [Fin.sum_univ_add]; simp
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · obtain ⟨hB, hp⟩ := hp₁ i
      exact ⟨by simpa using hB, by simpa using hp⟩
    · obtain ⟨hB, hp⟩ := hp₂ i
      exact ⟨by simpa using hB, by simpa using hp⟩
  · rw [Fin.sum_univ_add]; simp

/-- If `G` is an `ℝ`-Cartier pullback of `D` along `f`, then `a • G` is an `ℝ`-Cartier pullback of
`a • D`. -/
theorem isRCartierPullback_smul {f : Y ⟶ X} {D : RDivisor X} {G : RDivisor Y} (a : ℝ)
    (h : MMP.Flips.IsRCartierPullback f D G) :
    MMP.Flips.IsRCartierPullback f (a • D) (a • G) := by
  obtain ⟨m, r, L, L', hc, rfl, hp, rfl⟩ := h
  refine ⟨m, fun j => a * r j, L, L', hc, ?_, hp, ?_⟩
  · rw [Finset.smul_sum]; simp [mul_smul]
  · rw [Finset.smul_sum]; simp [mul_smul]

/-- If each `G i` is an `ℝ`-Cartier pullback of `D i` along `f`, then `∑ i ∈ s, G i` is an
`ℝ`-Cartier pullback of `∑ i ∈ s, D i`. -/
theorem isRCartierPullback_sum {ι : Type*} {f : Y ⟶ X} (s : Finset ι) (D : ι → RDivisor X)
    (G : ι → RDivisor Y) (h : ∀ i ∈ s, MMP.Flips.IsRCartierPullback f (D i) (G i)) :
    MMP.Flips.IsRCartierPullback f (∑ i ∈ s, D i) (∑ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isRCartierPullback_zero f
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact isRCartierPullback_add (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- If `C'` is the pullback along `f` of a Cartier divisor `C`, then `C'` is an `ℝ`-Cartier
pullback of `C` as `ℝ`-divisors. -/
theorem isRCartierPullback_toRDivisor {f : Y ⟶ X} {C : Divisor X} {C' : Divisor Y}
    (hC : C.IsCartier) (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ C.supp)
    (hp : C.IsPullback f hB C') :
    MMP.Flips.IsRCartierPullback f (Divisor.toRDivisor C) (Divisor.toRDivisor C') :=
  ⟨1, fun _ => 1, fun _ => C, fun _ => C', fun _ => hC, by simp, fun _ => ⟨hB, hp⟩, by simp⟩

end RPullbackAlgebra

section RPullbackPrincipal

variable {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y] [CompactSpace T] [CompactSpace Y]
  [IsLocallyNoetherian T] [IsNormal T] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The pull-back of `D + ∑ aⱼ div gⱼ` is `G + ∑ aⱼ div (f^*gⱼ)`, where `G` is a pull-back
of `D`. -/
theorem isRCartierPullback_add_sum_principal (f : T ⟶ Y) [IsDominant f] {D : RDivisor Y}
    {G : RDivisor T} (h : MMP.Flips.IsRCartierPullback f D G) {s : ℕ} (a : Fin s → ℝ)
    (g : Fin s → (RationalFunctions Y)ˣ) :
    MMP.Flips.IsRCartierPullback f
      (D + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor (g j)))
      (G + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor
        (pullbackRationalFunction f (g j)
          (map_componentGenericPoint_notMem_supp_of_isDominant f _)))) :=
  isRCartierPullback_add h (isRCartierPullback_sum _ _ _ fun j _ =>
    isRCartierPullback_smul _ (isRCartierPullback_toRDivisor (Divisor.isCartier_principalDivisor _)
      (map_componentGenericPoint_notMem_supp_of_isDominant f _)
      (Divisor.isPullback_principalDivisor (g j) _)))

omit [CompactSpace T] [CompactSpace Y] in
/-- **Local effectivity of real pull-backs.** If `L` is `ℝ`-Cartier, effective on an open `V`,
then each pull-back `G` of `L` along a dominant morphism `h` is effective along every prime
divisor meeting `h⁻¹V`. -/
theorem coeff_nonneg_of_isRCartierPullback_of_isEffectiveOn (h : T ⟶ Y) [IsDominant h]
    {L : RDivisor Y} {G : RDivisor T} (hG : MMP.Flips.IsRCartierPullback h L G) {V : Y.Opens}
    (hV : ∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ V).Nonempty → 0 ≤ L.coeff P)
    (Γ : MMP.Mori.PrimeDivisor T) (hΓ : (Γ.support ∩ h ⁻¹ᵁ V).Nonempty) : 0 ≤ G.coeff Γ := by
  obtain ⟨m, r, C, C', hC, hLeq, hp, rfl⟩ := hG
  have hp' : ∀ j, (C j).IsPullback h
      (map_componentGenericPoint_notMem_supp_of_isDominant h _) (C' j) := fun j => (hp j).2
  rw [coeff_sum_smul_toRDivisor]
  have hG : ∑ j, r j * ((C' j).coeff Γ : ℝ) = ∑ j, ((C' j).coeff Γ : ℝ) * r j :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hG]
  refine sum_mul_nonneg_of_forall_int
    (ι := {P : MMP.Mori.PrimeDivisor Y // (P.support ∩ V).Nonempty})
    (fun P j => (C j).coeff P.1) (fun j => (C' j).coeff Γ) r ?_ ?_ ?_
  · have hfS : (⋃ j : Fin m, ((C j).support : Set (MMP.Mori.PrimeDivisor Y))).Finite :=
      Set.finite_iUnion fun j => (C j).support.finite_toSet
    refine (hfS.preimage Subtype.val_injective.injOn).subset ?_
    intro P hP
    obtain ⟨j, hj⟩ : ∃ j, (C j).coeff P.1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hP (funext hcon)
    exact Set.mem_iUnion.2 ⟨j, Finsupp.mem_support_iff.mpr hj⟩
  · intro n hn
    have hBV : ∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ V).Nonempty →
        0 ≤ (∑ j, n j • C j).coeff P := fun P hP => by
      rw [coeff_sum_zsmul]
      simpa [mul_comm] using hn ⟨P, hP⟩
    have := coeff_nonneg_of_isPullback_of_isEffectiveOn (V := V)
      (isCartier_sum_zsmul n hC Finset.univ) hBV
      (isPullback_sum_zsmul h n hC hp' Finset.univ) Γ hΓ
    rw [coeff_sum_zsmul] at this
    simpa [mul_comm] using this
  · intro P
    have : 0 ≤ L.coeff P.1 := hV P.1 P.2
    rw [hLeq, coeff_sum_smul_toRDivisor] at this
    simpa [mul_comm] using this

end RPullbackPrincipal

section CoeffTransfer

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- The coefficient of a pull-back `G` of an `ℝ`-Cartier divisor `D` along a prime divisor `E`
mapping birationally onto a prime divisor `P` is the coefficient of `P` in `D`. -/
theorem coeff_eq_of_isRCartierPullback {f : X ⟶ Y} (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] {D : RDivisor Y} {G : RDivisor X}
    (h : MMP.Flips.IsRCartierPullback f D G) : G.coeff E = D.coeff P := by
  obtain ⟨m, r, C, C', hC, rfl, hp, rfl⟩ := h
  rw [coeff_sum_smul_toRDivisor, coeff_sum_smul_toRDivisor]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨hB, hj⟩ := hp j
  rw [MMP.Positivity.coeff_eq_of_isPullback E P heq (hC j) hj]

end CoeffTransfer

section GoodModel

variable {k : Type u} [Field k] {X Y T Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
  [IsIntegral X] [IsIntegral Y] [IsIntegral T]
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsLocallyNoetherian T] [IsNormal T] [CompactSpace X] [CompactSpace Y] [CompactSpace T]

/-- A prime divisor of `X` with positive coefficient in `p_*E` lies in the relative divisorial
stable base locus of `D`, where `p^*D = q^*D' + E` and `q_*E = 0`. -/
theorem isInRelativeDivisorialStableBase_of_pos_transformDivisor
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (hT : IsNormalVariety k sT)
    (p : T ⟶ X) (q : T ⟶ Y) (fX : X ⟶ Z) (fY : Y ⟶ Z)
    [IsProper p] [IsProper q] (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hqY : q ≫ sY = sT) (hZc : p ≫ fX = q ≫ fY)
    {D : RDivisor X} {D' : RDivisor Y} {GD GD' E : RDivisor T}
    (hGD : MMP.Flips.IsRCartierPullback p D GD) (hGD' : MMP.Flips.IsRCartierPullback q D' GD')
    (hpull : GD = GD' + E) (hqE : RationalMap.transformDivisor (X := T) q.toRationalMap E = 0)
    (G : MMP.Mori.PrimeDivisor X)
    (hpos : 0 < (RationalMap.transformDivisor (X := T) p.toRationalMap E).coeff G) :
    IsInRelativeDivisorialStableBase fX D G := by
  have := hp.isDominant
  have := hq.isDominant
  have hTX : IsNormalVariety k (p ≫ sX) := hpX ▸ hT
  have hTY : IsNormalVariety k (q ≫ sY) := hqY ▸ hT
  have hpt : ∀ t : T, fX (p t) = fY (q t) := fun t => by
    rw [← Scheme.Hom.comp_apply, hZc, Scheme.Hom.comp_apply]
  obtain ⟨G', hG'gen, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hTX hp G
  intro U hU s a g hLeff
  choose ψ _ hψeq using fun j => exists_pullbackRationalFunction_eq hq
    (pullbackRationalFunction p (g j) (map_componentGenericPoint_notMem_supp_of_isDominant p _))
  have hGL := isRCartierPullback_add_sum_principal p hGD a g
  have hGL' := isRCartierPullback_add_sum_principal q hGD' a ψ
  have hrel : GD + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor
        (pullbackRationalFunction p (g j)
          (map_componentGenericPoint_notMem_supp_of_isDominant p _))) =
      (GD' + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor
        (pullbackRationalFunction q (ψ j)
          (map_componentGenericPoint_notMem_supp_of_isDominant q _)))) + E := by
    rw [hpull]
    simp_rw [hψeq]
    abel
  have hLeff' : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ (fX ⁻¹ᵁ U : Set X)).Nonempty →
      0 ≤ (D + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor (g j))).coeff P :=
    hLeff
  have hmeetP : ∀ P' : MMP.Mori.PrimeDivisor T, ∀ P : MMP.Mori.PrimeDivisor Y,
      q P'.genericPoint = P.genericPoint → (P.support ∩ (fY ⁻¹ᵁ U : Set Y)).Nonempty →
      (P'.support ∩ (p ⁻¹ᵁ (fX ⁻¹ᵁ U) : Set T)).Nonempty := by
    intro P' P hgen hP
    refine (P'.genericPoint_mem_iff _).mp ?_
    change fX (p P'.genericPoint) ∈ U
    rw [hpt, hgen]
    exact (P.genericPoint_mem_iff (fY ⁻¹ᵁ U)).mpr hP
  have hL'eff : ∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ (fY ⁻¹ᵁ U : Set Y)).Nonempty →
      0 ≤ (D' + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor (ψ j))).coeff P := by
    intro P hP
    obtain ⟨P', hP'gen, hiso', htr'⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hY hTY hq P
    have hE0 : E.coeff P' = 0 := by
      have := htr' E
      rw [hqE] at this
      exact this.symm
    have h1 := coeff_nonneg_of_isRCartierPullback_of_isEffectiveOn p hGL hLeff' P'
      (hmeetP P' P hP'gen hP)
    rw [hrel, DivisorWithCoeffs.coeff_add, hE0, add_zero,
      coeff_eq_of_isRCartierPullback P' P hP'gen hGL'] at h1
    exact h1
  have hmeetG : (G'.support ∩ (q ⁻¹ᵁ (fY ⁻¹ᵁ U) : Set T)).Nonempty := by
    refine (G'.genericPoint_mem_iff _).mp ?_
    change fY (q G'.genericPoint) ∈ U
    rw [← hpt, hG'gen]
    exact hU
  have h2 := coeff_nonneg_of_isRCartierPullback_of_isEffectiveOn q hGL' hL'eff G' hmeetG
  have h3 := coeff_eq_of_isRCartierPullback G' G hG'gen hGL
  change 0 < (D + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor (g j))).coeff G
  rw [← h3, hrel, DivisorWithCoeffs.coeff_add]
  have h4 : (RationalMap.transformDivisor (X := T) p.toRationalMap E).coeff G = E.coeff G' :=
    htr E
  rw [h4] at hpos
  exact lt_of_lt_of_le hpos (le_add_of_nonneg_left h2)

/-- A prime divisor of the relative divisorial stable base locus of `D` has positive coefficient in
`p_*E`, where `p^*D = q^*D' + E`, `E ≥ 0`, and `D'` is a nonnegative real combination
of relatively free Cartier divisors up to a real combination of principal divisors. -/
theorem pos_transformDivisor_of_isInRelativeDivisorialStableBase
    (hX : IsNormalVariety k sX) (hT : IsNormalVariety k sT)
    (p : T ⟶ X) (q : T ⟶ Y) (fX : X ⟶ Z) (fY : Y ⟶ Z)
    [IsProper p] [IsProper q] (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hZc : p ≫ fX = q ≫ fY)
    {D : RDivisor X} {D' : RDivisor Y} {GD GD' E : RDivisor T}
    (hGD : MMP.Flips.IsRCartierPullback p D GD) (hGD' : MMP.Flips.IsRCartierPullback q D' GD')
    (hpull : GD = GD' + E) (hE : 0 ≤ E)
    {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (H : Fin m → Divisor Y)
    (hHc : ∀ i, (H i).IsCartier) (hHfree : ∀ i, IsRelativelyFreeDivisor fY (H i))
    {s₀ : ℕ} (b : Fin s₀ → ℝ) (h : Fin s₀ → (RationalFunctions Y)ˣ)
    (hlin : D' = ∑ i, c i • Divisor.toRDivisor (H i) +
      ∑ j, b j • Divisor.toRDivisor (MMP.Mori.principalDivisor (h j)))
    (G : MMP.Mori.PrimeDivisor X) (hG : IsInRelativeDivisorialStableBase fX D G) :
    0 < (RationalMap.transformDivisor (X := T) p.toRationalMap E).coeff G := by
  classical
  have := hp.isDominant
  have := hq.isDominant
  have hTX : IsNormalVariety k (p ≫ sX) := hpX ▸ hT
  have hpt : ∀ t : T, fX (p t) = fY (q t) := fun t => by
    rw [← Scheme.Hom.comp_apply, hZc, Scheme.Hom.comp_apply]
  obtain ⟨G', hG'gen, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hTX hp G
  have h4 : (RationalMap.transformDivisor (X := T) p.toRationalMap E).coeff G = E.coeff G' :=
    htr E
  rw [h4]
  by_contra hneg
  have hEG : E.coeff G' = 0 := le_antisymm (not_lt.mp hneg) (hE G')
  -- local generating sections of the relatively free divisors
  choose U hUy ψ hψeff hψ0 using fun i =>
    exists_coeff_add_ord_eq_zero_of_isRelativelyFree fY (hHc i) (hHfree i) (q G'.genericPoint)
  let U₀ : Z.Opens := Finset.univ.inf U
  have hU₀ : fY (q G'.genericPoint) ∈ U₀ := by
    have : ∀ i ∈ (Finset.univ : Finset (Fin m)), fY (q G'.genericPoint) ∈ (U i : Set Z) :=
      fun i _ => hUy i
    change fY (q G'.genericPoint) ∈ (U₀ : Set Z)
    rw [TopologicalSpace.Opens.coe_finset_inf]
    simpa [Finset.inf_eq_iInf] using this
  have hU₀le : ∀ i, U₀ ≤ U i := fun i => Finset.inf_le (Finset.mem_univ i)
  have hUG : fX G.genericPoint ∈ U₀ := by rw [← hG'gen, hpt]; exact hU₀
  -- the combined representatives
  let a : Fin (s₀ + m) → ℝ := Fin.append (fun j => - b j) c
  let gY : Fin (s₀ + m) → (RationalFunctions Y)ˣ := Fin.append h ψ
  choose φ _ hφeq using fun j : Fin (s₀ + m) => exists_pullbackRationalFunction_eq hp
    (pullbackRationalFunction q (gY j) (map_componentGenericPoint_notMem_supp_of_isDominant q _))
  let M : RDivisor Y := ∑ i, c i • Divisor.toRDivisor (H i + MMP.Mori.principalDivisor (ψ i))
  have hLM : D' + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor (gY j)) = M := by
    simp only [M, a, gY, Fin.sum_univ_add, Fin.append_left, Fin.append_right, neg_smul, map_add,
      smul_add, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [hlin]
    abel
  have hB' : ∀ i, ∀ W : irreducibleComponents T,
      q (componentGenericPoint T W) ∉ (H i).supp := fun i =>
    map_componentGenericPoint_notMem_supp_of_isDominant q _
  have hMp : MMP.Flips.IsRCartierPullback q M
      (∑ i, c i • Divisor.toRDivisor ((H i).pullback (hHc i) (hB' i) +
        MMP.Mori.principalDivisor (pullbackRationalFunction q (ψ i)
          (map_componentGenericPoint_notMem_supp_of_isDominant q _)))) :=
    isRCartierPullback_sum _ _ _ fun i _ => isRCartierPullback_smul _
      (isRCartierPullback_toRDivisor ((hHc i).add (Divisor.isCartier_principalDivisor _))
        (map_componentGenericPoint_notMem_supp_of_isDominant q _)
        (Divisor.IsPullback.add (hHc i) (Divisor.isCartier_principalDivisor _) _
          (Divisor.isPullback_pullback (hHc i) (hB' i))
          (Divisor.isPullback_principalDivisor (ψ i) _)))
  set GM : RDivisor T := ∑ i, c i • Divisor.toRDivisor ((H i).pullback (hHc i) (hB' i) +
        MMP.Mori.principalDivisor (pullbackRationalFunction q (ψ i)
          (map_componentGenericPoint_notMem_supp_of_isDominant q _))) with hGMdef
  have hGL := isRCartierPullback_add_sum_principal p hGD a φ
  have hGL' := isRCartierPullback_add_sum_principal q hGD' a gY
  rw [hLM] at hGL'
  have hGMeq : GD' + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor
      (pullbackRationalFunction q (gY j)
        (map_componentGenericPoint_notMem_supp_of_isDominant q _))) = GM :=
    MMP.Flips.IsRCartierPullback.eq q hGL' hMp
  have hrel : GD + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor
        (pullbackRationalFunction p (φ j)
          (map_componentGenericPoint_notMem_supp_of_isDominant p _))) = GM + E := by
    rw [hpull, ← hGMeq]
    simp_rw [hφeq]
    abel
  -- effectiveness of `M` over `U₀`
  have hMeff : ∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ (fY ⁻¹ᵁ U₀ : Set Y)).Nonempty →
      0 ≤ M.coeff P := by
    intro P hP
    simp only [M]
    rw [coeff_sum_smul_toRDivisor]
    refine Finset.sum_nonneg fun i _ => mul_nonneg (hc i) ?_
    have := hψeff i P (hP.mono (Set.inter_subset_inter_right _ (fun x hx => hU₀le i hx)))
    have h5 : ((H i + MMP.Mori.principalDivisor (ψ i)).coeff P : ℝ) =
        ((H i).coeff P + P.ord (ψ i) : ℤ) := rfl
    rw [h5]
    exact_mod_cast this
  have hLeff : IsEffectiveOn (D + ∑ j, a j • Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
      (MMP.Mori.principalDivisor (φ j))) (fX ⁻¹ᵁ U₀) := by
    intro P hP
    obtain ⟨P', hP'gen, hiso', htr'⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hTX hp P
    have hmeet : (P'.support ∩ (q ⁻¹ᵁ (fY ⁻¹ᵁ U₀) : Set T)).Nonempty := by
      refine (P'.genericPoint_mem_iff _).mp ?_
      change fY (q P'.genericPoint) ∈ U₀
      rw [← hpt, hP'gen]
      exact (P.genericPoint_mem_iff (fX ⁻¹ᵁ U₀)).mpr hP
    have h1 := coeff_nonneg_of_isRCartierPullback_of_isEffectiveOn q hMp hMeff P' hmeet
    have h2 := coeff_eq_of_isRCartierPullback P' P hP'gen hGL
    rw [hrel, DivisorWithCoeffs.coeff_add] at h2
    change 0 ≤ (D + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor (φ j))).coeff P
    rw [← h2]
    exact add_nonneg h1 (hE P')
  have hpos := hG U₀ hUG _ a φ hLeff
  change 0 < (D + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor (φ j))).coeff G at hpos
  rw [← coeff_eq_of_isRCartierPullback G' G hG'gen hGL, hrel, DivisorWithCoeffs.coeff_add,
    hEG, add_zero] at hpos
  -- the coefficient of `GM` along `G'` vanishes
  have hGM0 : GM.coeff G' = 0 := by
    rw [hGMdef, coeff_sum_smul_toRDivisor]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hG'0 : ((H i).pullback (hHc i) (hB' i) + MMP.Mori.principalDivisor
        (pullbackRationalFunction q (ψ i)
          (map_componentGenericPoint_notMem_supp_of_isDominant q _))).coeff G' = 0 := by
      by_contra hne
      have hmem : G'.genericPoint ∈ ((H i).pullback (hHc i) (hB' i) + MMP.Mori.principalDivisor
          (pullbackRationalFunction q (ψ i)
            (map_componentGenericPoint_notMem_supp_of_isDominant q _))).supp :=
        DivisorWithCoeffs.mem_supp_iff.mpr ⟨G', hne, by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact subset_closure rfl⟩
      have hy := MMP.Flips.supp_subset_preimage_supp_of_isPullback
        (hB := map_componentGenericPoint_notMem_supp_of_isDominant q _)
        ((hHc i).add (Divisor.isCartier_principalDivisor _))
        (Divisor.IsPullback.add (hHc i) (Divisor.isCartier_principalDivisor _) _
          (Divisor.isPullback_pullback (hHc i) (hB' i))
          (Divisor.isPullback_principalDivisor (ψ i)
            (map_componentGenericPoint_notMem_supp_of_isDominant q _))) hmem
      obtain ⟨P, hP0, hyP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
      apply hP0
      rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
      exact hψ0 i P hyP
    rw [hG'0]
    simp
  have hfinal : (D + ∑ j, a j • Divisor.toRDivisor (MMP.Mori.principalDivisor (φ j))).coeff G =
      0 := by
    rw [← coeff_eq_of_isRCartierPullback G' G hG'gen hGL, hrel, DivisorWithCoeffs.coeff_add,
      hGM0, hEG, add_zero]
  linarith

/-- **Stable base primes of a given good birational model.** Let `p : T ⟶ X` and `q : T ⟶ Y` be
proper birational morphisms of normal varieties over `k`, compatible with morphisms `fX, fY`
to `Z` (`p ≫ fX = q ≫ fY`), and let `D, D'` be `ℝ`-Cartier divisors on `X, Y` with
`p^*D = q^*D' + E` (`GD`, `GD'` the pull-backs of `D`, `D'`, `MMP.Flips.IsRCartierPullback`),
`E ≥ 0` and `q_*E = 0`. Suppose `D'` is `ℝ`-linearly equivalent over `Z` to a nonnegative real
combination `∑ cᵢ Hᵢ` of integral Cartier divisors `Hᵢ` that are relatively free over `Z`: here
`ℝ`-linear equivalence is the one in the definition of the relative divisorial stable base locus
(`MMP.Fourfold.IsInRelativeDivisorialStableBase`), `D' = ∑ cᵢ Hᵢ + ∑ bⱼ div hⱼ` with `hⱼ ∈ K(Y)^×`.
Then the prime divisors in the relative divisorial stable base locus of `D` (for `fX`) are exactly
the primes with positive coefficient in `p_*E`. -/
@[mmp "lem_fourfold_good_model_base_primes"]
theorem isInRelativeDivisorialStableBase_iff_pos_transformDivisor
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (hT : IsNormalVariety k sT)
    (p : T ⟶ X) (q : T ⟶ Y) (fX : X ⟶ Z) (fY : Y ⟶ Z)
    [IsProper p] [IsProper q] (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hqY : q ≫ sY = sT) (hZc : p ≫ fX = q ≫ fY)
    {D : RDivisor X} {D' : RDivisor Y} {GD GD' E : RDivisor T}
    (hGD : MMP.Flips.IsRCartierPullback p D GD) (hGD' : MMP.Flips.IsRCartierPullback q D' GD')
    (hpull : GD = GD' + E) (hE : 0 ≤ E)
    (hqE : RationalMap.transformDivisor (X := T) q.toRationalMap E = 0)
    {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (H : Fin m → Divisor Y)
    (hHc : ∀ i, (H i).IsCartier) (hHfree : ∀ i, IsRelativelyFreeDivisor fY (H i))
    {s₀ : ℕ} (b : Fin s₀ → ℝ) (h : Fin s₀ → (RationalFunctions Y)ˣ)
    (hlin : D' = ∑ i, c i • Divisor.toRDivisor (H i) +
      ∑ j, b j • Divisor.toRDivisor (MMP.Mori.principalDivisor (h j)))
    (G : MMP.Mori.PrimeDivisor X) :
    IsInRelativeDivisorialStableBase fX D G ↔
      0 < (RationalMap.transformDivisor (X := T) p.toRationalMap E).coeff G :=
  ⟨pos_transformDivisor_of_isInRelativeDivisorialStableBase hX hT p q fX fY hp hq hpX hZc
      hGD hGD' hpull hE c hc H hHc hHfree b h hlin G,
    isInRelativeDivisorialStableBase_of_pos_transformDivisor hX hY hT p q fX fY hp hq hpX hqY hZc
      hGD hGD' hpull hqE G⟩

end GoodModel

section KltSub

variable {k : Type u} [Field k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- Adding a nonnegative multiple of a prime divisor on a smooth variety does not increase a log
discrepancy. -/
theorem exists_isLogDiscrepancy_add_single_le (hsm : IsSmoothScheme sX) {n : ℕ} {B : RDivisor X}
    {D : DivisorOver k sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a)
    (P : MMP.Mori.PrimeDivisor X) {c : ℝ} (hc : 0 ≤ c) :
    ∃ a' : ℝ, a' ≤ a ∧
      MMP.Intersection.IsLogDiscrepancy sX n (B + Finsupp.single P c) D a' := by
  classical
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isIntegral
  have := D.isBirationalMorphism.isDominant
  have : CompactSpace D.Y := (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨hnv, hprop, ω, hω0, hK, m, r, C, C', hC, hrel, hpb, ha⟩ := h
  have hC₀ : Divisor.IsCartier (Finsupp.single P 1 : Divisor X) :=
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P
  obtain ⟨C₀', hC₀'⟩ := hC₀.exists_isPullback
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _)
  have hnn : 0 ≤ C₀'.coeff D.E := by
    refine MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) hC₀
      (fun P' _ => ?_) hC₀' D.E ((D.E.genericPoint_mem_iff _).mp trivial)
    change (0 : ℤ) ≤ (Finsupp.single P (1 : ℤ)) P'
    rw [Finsupp.single_apply]
    split_ifs <;> simp
  refine ⟨a - c * (C₀'.coeff D.E : ℝ), ?_, hnv, hprop, ω, hω0, hK, m + 1, Fin.snoc r c,
    Fin.snoc C (Finsupp.single P 1), Fin.snoc C' C₀', ?_, ?_, ?_, ?_⟩
  · linarith [mul_nonneg hc (show (0 : ℝ) ≤ C₀'.coeff D.E by exact_mod_cast hnn)]
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hC₀
    · simpa using hC j
  · intro Γ
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, DivisorWithCoeffs.coeff_add, ← hrel Γ]
    have : ((DivisorWithCoeffs.coeff (R := ℤ) (Finsupp.single P (1 : ℤ) : Divisor X) Γ : ℤ) : ℝ) =
        (if P = Γ then 1 else 0) := by
      change ((Finsupp.single P (1 : ℤ)) Γ : ℝ) = _
      rw [Finsupp.single_apply]
      split_ifs <;> simp
    rw [this]
    have h2 : DivisorWithCoeffs.coeff (Finsupp.single P c : RDivisor X) Γ =
        if P = Γ then c else 0 := by
      change (Finsupp.single P c) Γ = _
      rw [Finsupp.single_apply]
    rw [h2]
    split_ifs <;> simp [add_assoc]
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hB := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f
        (Finsupp.single P (1 : ℤ) : Divisor X)
      refine ⟨by simpa using hB, ?_⟩
      simpa using hC₀'
    · simpa using hpb j
  · rw [Fin.sum_univ_castSucc, ha]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

/-- Adding an effective `ℚ`-divisor on a smooth variety does not increase a log discrepancy. -/
theorem exists_isLogDiscrepancy_add_le (hsm : IsSmoothScheme sX) {n : ℕ}
    {D : DivisorOver k sX} (Δ : QDivisor X) (hΔ : ∀ P, 0 ≤ Δ.coeff P) {B : RDivisor X} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) :
    ∃ a' : ℝ, a' ≤ a ∧
      MMP.Intersection.IsLogDiscrepancy sX n (B + QDivisor.toRDivisor Δ) D a' := by
  classical
  suffices H : ∀ Δ : MMP.Mori.PrimeDivisor X →₀ ℚ, (∀ P, 0 ≤ Δ P) → ∀ (B : RDivisor X) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n B D a → ∃ a' : ℝ, a' ≤ a ∧
        MMP.Intersection.IsLogDiscrepancy sX n
          (B + QDivisor.toRDivisor (show QDivisor X from Δ)) D a' from H Δ hΔ B a h
  intro Δ
  refine Finsupp.induction Δ ?_ ?_
  · intro _ B a h
    refine ⟨a, le_rfl, ?_⟩
    have : QDivisor.toRDivisor (show QDivisor X from (0 : MMP.Mori.PrimeDivisor X →₀ ℚ)) = 0 :=
      map_zero _
    rwa [this, add_zero]
  · intro P c f hP hc ih hnn B a h
    have hc0 : 0 ≤ c := by
      have := hnn P
      rwa [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hP,
        add_zero] at this
    have hf0 : ∀ Q, 0 ≤ f Q := fun Q => by
      have := hnn Q
      by_cases hQ : P = Q
      · subst hQ
        rw [Finsupp.notMem_support_iff.mp hP]
      · simpa [Finsupp.single_apply, hQ] using this
    obtain ⟨a₁, ha₁, h₁⟩ := exists_isLogDiscrepancy_add_single_le hsm h P (c := (c : ℝ))
      (by exact_mod_cast hc0)
    obtain ⟨a₂, ha₂, h₂⟩ := ih hf0 _ a₁ h₁
    refine ⟨a₂, ha₂.trans ha₁, ?_⟩
    have : QDivisor.toRDivisor (show QDivisor X from (Finsupp.single P c + f)) =
        Finsupp.single P (c : ℝ) + QDivisor.toRDivisor (show QDivisor X from f) := by
      have h3 : QDivisor.toRDivisor (show QDivisor X from (Finsupp.single P c + f)) =
          QDivisor.toRDivisor (show QDivisor X from (Finsupp.single P c)) +
            QDivisor.toRDivisor (show QDivisor X from f) := map_add _ _ _
      rw [h3]
      congr 1
      ext Γ
      change ((((Finsupp.single P c : MMP.Mori.PrimeDivisor X →₀ ℚ) Γ : ℚ)) : ℝ) =
        (Finsupp.single P (c : ℝ) : MMP.Mori.PrimeDivisor X →₀ ℝ) Γ
      by_cases hΓ : P = Γ
      · subst hΓ
        rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      · rw [Finsupp.single_eq_of_ne (Ne.symm hΓ), Finsupp.single_eq_of_ne (Ne.symm hΓ)]
        simp
    rwa [this, ← add_assoc]

omit [IsIntegral X] in
/-- On a smooth variety every divisor is Cartier. -/
theorem isCartier_of_isSmoothScheme (hsm : IsSmoothScheme sX) (D : Divisor X) :
    D.IsCartier := by
  induction D using Finsupp.induction_linear with
  | zero => exact Divisor.isCartier_zero
  | add f g hf hg => exact hf.add hg
  | single E n =>
    have := (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm E).zsmul n
    simpa [Finsupp.smul_single] using this

omit [IsIntegral X] in
/-- On a smooth variety every `ℚ`-divisor is `ℚ`-Cartier. -/
theorem isQCartier_of_isSmoothScheme (hsm : IsSmoothScheme sX) (D : QDivisor X) :
    D.IsQCartier := by
  classical
  set m : ℕ := ∏ E ∈ D.support, (D E).den with hm
  have hint : ∀ E, ∃ n : ℤ, ((m : ℤ) • D).coeff E = n := by
    intro E
    by_cases hE : E ∈ D.support
    · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun E => (D E).den) hE
      refine ⟨(c : ℤ) * (D E).num, ?_⟩
      rw [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, DivisorWithCoeffs.coeff_apply]
      have h1 : ((D E).den : ℚ) * D E = (D E).num := Rat.den_mul_eq_num _
      have h2 : (m : ℚ) = ((D E).den : ℚ) * c := by exact_mod_cast hc
      push_cast
      rw [h2, ← h1]
      ring
    · refine ⟨0, ?_⟩
      rw [Finsupp.notMem_support_iff] at hE
      simp [DivisorWithCoeffs.coeff_apply, hE]
  have hmpos : 0 < m := Finset.prod_pos fun E _ => (D E).den_pos
  obtain ⟨D', hD'⟩ := (QDivisor.mem_range_toQDivisor_iff _).2 hint
  exact ⟨m, by exact_mod_cast hmpos.ne', ⟨D', hD', isCartier_of_isSmoothScheme hsm D'⟩⟩

/-- **Klt is preserved by subtracting an effective `ℚ`-divisor on a smooth variety.** If `(X, Ω)`
is klt (`MMP.Fourfold.IsKltPair`) and `0 ≤ Δ ≤ Ω` is a `ℚ`-divisor on a smooth variety `X`, then
`(X, Ω - Δ)` is klt. -/
theorem isKltPair_sub_of_isSmoothScheme (hsm : IsSmoothScheme sX) {Ω Δ : QDivisor X}
    (hΩ : IsKltPair sX Ω) (hΔ0 : ∀ P, 0 ≤ Δ.coeff P) (hΔΩ : ∀ P, Δ.coeff P ≤ Ω.coeff P) :
    IsKltPair sX (Ω - Δ) := by
  obtain ⟨⟨hac, hcz, ⟨hnv, n, K, hK, -⟩, -⟩, hlog⟩ := hΩ
  refine ⟨⟨hac, hcz, ⟨hnv, n, K, hK, isQCartier_of_isSmoothScheme hsm _⟩, fun P => ?_⟩, ?_⟩
  · rw [DivisorWithCoeffs.coeff_sub]
    linarith [hΔΩ P]
  · intro n' D a ha
    have hΩsum : QDivisor.toRDivisor (Ω - Δ) + QDivisor.toRDivisor Δ = QDivisor.toRDivisor Ω := by
      rw [← map_add, sub_add_cancel]
    obtain ⟨a', ha', hlog'⟩ := exists_isLogDiscrepancy_add_le hsm Δ hΔ0 ha
    rw [hΩsum] at hlog'
    exact lt_of_lt_of_le (hlog n' D a' hlog') ha'

end KltSub

section Series

variable {S : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]

/-- The integral divisor `m K + ⌊m Ω⌋` whose sections `V_m` live in; it is `m (K + Ω)` for `m`
divisible by the index of `Ω`. -/
abbrev seriesDivisor (K : Divisor S) (Ω : QDivisor S) (m : ℕ) : Divisor S :=
  m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Ω)

omit [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S] in
/-- The coefficient of `m K + ⌊m Ω⌋` along `P` is `m K_P + ⌊m Ω_P⌋`. -/
theorem coeff_seriesDivisor (K : Divisor S) (Ω : QDivisor S) (m : ℕ) (P : MMP.Mori.PrimeDivisor S) :
    (seriesDivisor K Ω m).coeff P = m * K.coeff P + ⌊(m : ℚ) * Ω.coeff P⌋ := by
  simp [seriesDivisor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundDown,
    DivisorWithCoeffs.coeff_smul]

/-- A nonzero section of `𝒪_S(D)` is a unit `χ` of `K(S)` with `D + div χ ≥ 0`. -/
theorem exists_unit_of_mem_divisorialSections {D : Divisor S} {s : RationalFunctions S}
    (hs : s ∈ divisorialSections D) (h0 : s ≠ 0) :
    ∃ χ : (RationalFunctions S)ˣ, (χ : RationalFunctions S) = s ∧
      ∀ P : MMP.Mori.PrimeDivisor S, 0 ≤ D.coeff P + P.ord χ := by
  let σ : D.divisorialSubmodule ⊤ := ⟨(rationalFunctionsPresheafTopEquiv S).symm s, hs⟩
  have hσ : σ ≠ 0 := by
    intro h
    apply h0
    have h1 : (rationalFunctionsPresheafTopEquiv S) σ.1 = s :=
      (rationalFunctionsPresheafTopEquiv S).apply_symm_apply s
    rw [← h1, h]
    simp
  obtain ⟨χ, hχ, hχe⟩ := exists_unit_of_divisorialSubmodule_ne_zero
    (⟨(genericPoint S : S), trivial⟩ : ((⊤ : S.Opens) : Set S).Nonempty) σ hσ
  refine ⟨χ, ?_, fun P => hχe P (primeDivisor_support_inter_top_nonempty P)⟩
  funext Z
  exact (hχ Z trivial).symm

/-- The vanishing order along `G` of a section `s = χ` of `𝒪(D)` is `(D_G + ord_G χ).toNat`. -/
theorem sectionVanishingOrder_eq_of_unit {D : Divisor S} {s : RationalFunctions S}
    (hs : s ∈ divisorialSections D) {χ : (RationalFunctions S)ˣ}
    (hχ : (χ : RationalFunctions S) = s)
    (G : MMP.Mori.PrimeDivisor S) :
    sectionVanishingOrder D G (primeDivisor_support_inter_top_nonempty G)
      ⟨(rationalFunctionsPresheafTopEquiv S).symm s, hs⟩ = ((D.coeff G + G.ord χ).toNat : ℕ∞) :=
  sectionVanishingOrder_eq_toNat _ _ χ (by rw [hχ]; rfl)

end Series

section SeriesFixed

variable {S : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  {R : Type*} [Semiring R] [Module R (RationalFunctions S)]

/-- If `qΩ` is integral then `mΩ` has integral coefficients for `q ∣ m`. -/
theorem exists_int_eq_mul_coeff_of_isCartierDivisor {Ω : QDivisor S} {q : ℕ}
    (h : ((q : ℤ) • Ω).IsCartierDivisor) {m : ℕ} (hm : q ∣ m) (P : MMP.Mori.PrimeDivisor S) :
    ∃ z : ℤ, (m : ℚ) * Ω.coeff P = z := by
  obtain ⟨D', hD', -⟩ := h
  obtain ⟨c, rfl⟩ := hm
  refine ⟨c * D'.coeff P, ?_⟩
  have := congrArg (fun F : QDivisor S => F.coeff P) hD'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast] at this
  push_cast
  rw [this]
  ring

omit [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S] in
/-- If `m Ω` has integral coefficients, then the coefficients of `seriesDivisor K Ω (a * m)` are
`a` times those of `seriesDivisor K Ω m`. -/
theorem coeff_seriesDivisor_mul {K : Divisor S} {Ω : QDivisor S} {m : ℕ}
    (hint : ∀ P : MMP.Mori.PrimeDivisor S, ∃ z : ℤ, (m : ℚ) * Ω.coeff P = z) (a : ℕ)
    (P : MMP.Mori.PrimeDivisor S) :
    (seriesDivisor K Ω (a * m)).coeff P = a * (seriesDivisor K Ω m).coeff P := by
  obtain ⟨z, hz⟩ := hint P
  rw [coeff_seriesDivisor, coeff_seriesDivisor]
  have : ((a * m : ℕ) : ℚ) * Ω.coeff P = ((a * z : ℤ) : ℚ) := by
    push_cast; rw [mul_assoc, hz]
  rw [this, hz, Int.floor_intCast, Int.floor_intCast]
  push_cast
  ring

omit [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S] in
/-- If `m Ω` and `n Ω` have integral coefficients, then the coefficients of
`seriesDivisor K Ω (m + n)` are the sums of those of `seriesDivisor K Ω m` and
`seriesDivisor K Ω n`. -/
theorem coeff_seriesDivisor_add {K : Divisor S} {Ω : QDivisor S} {m n : ℕ}
    (hm : ∀ P : MMP.Mori.PrimeDivisor S, ∃ z : ℤ, (m : ℚ) * Ω.coeff P = z)
    (hn : ∀ P : MMP.Mori.PrimeDivisor S, ∃ z : ℤ, (n : ℚ) * Ω.coeff P = z)
    (P : MMP.Mori.PrimeDivisor S) :
    (seriesDivisor K Ω (m + n)).coeff P =
      (seriesDivisor K Ω m).coeff P + (seriesDivisor K Ω n).coeff P := by
  obtain ⟨z, hz⟩ := hm P
  obtain ⟨w, hw⟩ := hn P
  rw [coeff_seriesDivisor, coeff_seriesDivisor, coeff_seriesDivisor]
  have : ((m + n : ℕ) : ℚ) * Ω.coeff P = ((z + w : ℤ) : ℚ) := by
    push_cast; rw [add_mul, hz, hw]
  rw [this, hz, hw, Int.floor_intCast, Int.floor_intCast, Int.floor_intCast]
  push_cast
  ring

/-- The fixed multiplicity is at most the vanishing order of any nonzero section. -/
theorem restrictedFixedMultiplicity_le_toNat {K : Divisor S} {Ω : QDivisor S}
    {V : ℕ → Submodule R (RationalFunctions S)} {m : ℕ} {s : RationalFunctions S}
    (hsV : s ∈ V m) (hs : s ∈ divisorialSections (seriesDivisor K Ω m)) (h0 : s ≠ 0)
    {χ : (RationalFunctions S)ˣ} (hχ : (χ : RationalFunctions S) = s)
    (G : MMP.Mori.PrimeDivisor S) :
    restrictedFixedMultiplicity K Ω V m G ≤
      (((seriesDivisor K Ω m).coeff G + G.ord χ).toNat : ℕ∞) := by
  unfold restrictedFixedMultiplicity
  exact iInf_le_of_le s (iInf_le_of_le hsV (iInf_le_of_le hs (iInf_le_of_le h0
    (sectionVanishingOrder_eq_of_unit hs hχ G).le)))

/-- The fixed multiplicity of `V_m` is finite when `V_m ≠ 0`. -/
theorem restrictedFixedMultiplicity_ne_top {K : Divisor S} {Ω : QDivisor S}
    {V : ℕ → Submodule R (RationalFunctions S)} {m : ℕ}
    (hmem : ∀ s ∈ V m, s ∈ divisorialSections (seriesDivisor K Ω m))
    (hne : ∃ s ∈ V m, s ≠ 0) (G : MMP.Mori.PrimeDivisor S) :
    restrictedFixedMultiplicity K Ω V m G ≠ ⊤ := by
  obtain ⟨s, hsV, hs0⟩ := hne
  obtain ⟨χ, hχ, -⟩ := exists_unit_of_mem_divisorialSections (hmem s hsV) hs0
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _)
    (restrictedFixedMultiplicity_le_toNat hsV (hmem s hsV) hs0 hχ G)

omit [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S] in
/-- Powers of a section of `V_m` lie in `V_{bm}`. -/
theorem pow_mem_of_mul_mem {V : ℕ → Submodule R (RationalFunctions S)}
    (hmul : ∀ m n, ∀ s ∈ V m, ∀ t ∈ V n, s * t ∈ V (m + n)) {m : ℕ} {s : RationalFunctions S}
    (hsV : s ∈ V m) {b : ℕ} (hb : 0 < b) : s ^ b ∈ V (b * m) := by
  induction b, hb using Nat.le_induction with
  | base => simpa using hsV
  | succ b hb ih =>
    have := hmul _ _ _ ih _ hsV
    rw [pow_succ]
    convert this using 2
    ring

/-- The fixed multiplicity is attained by a nonzero section of `V_m`, when there is one. -/
theorem exists_restrictedFixedMultiplicity_eq {K : Divisor S} {Ω : QDivisor S}
    {V : ℕ → Submodule R (RationalFunctions S)} {m : ℕ}
    (hmem : ∀ s ∈ V m, s ∈ divisorialSections (seriesDivisor K Ω m))
    (hne : ∃ s ∈ V m, s ≠ 0) (G : MMP.Mori.PrimeDivisor S) :
    ∃ s ∈ V m, s ≠ 0 ∧ ∃ χ : (RationalFunctions S)ˣ, (χ : RationalFunctions S) = s ∧
      (∀ P : MMP.Mori.PrimeDivisor S, 0 ≤ (seriesDivisor K Ω m).coeff P + P.ord χ) ∧
      restrictedFixedMultiplicity K Ω V m G =
        (((seriesDivisor K Ω m).coeff G + G.ord χ).toNat : ℕ∞) := by
  have hx := restrictedFixedMultiplicity_ne_top hmem hne G
  have key : ∀ y : ℕ∞, restrictedFixedMultiplicity K Ω V m G < y →
      ∃ s, ∃ (hsV : s ∈ V m) (hs : s ∈ divisorialSections (seriesDivisor K Ω m)) (h0 : s ≠ 0),
        sectionVanishingOrder (seriesDivisor K Ω m) G (primeDivisor_support_inter_top_nonempty G)
          ⟨(rationalFunctionsPresheafTopEquiv S).symm s, hs⟩ < y := by
    intro y hy
    unfold restrictedFixedMultiplicity at hy
    rw [iInf_lt_iff] at hy
    obtain ⟨s, hy⟩ := hy
    rw [iInf_lt_iff] at hy
    obtain ⟨hsV, hy⟩ := hy
    rw [iInf_lt_iff] at hy
    obtain ⟨hs, hy⟩ := hy
    rw [iInf_lt_iff] at hy
    obtain ⟨h0, hy⟩ := hy
    exact ⟨s, hsV, hs, h0, hy⟩
  obtain ⟨s, hsV, hs, h0, hlt⟩ := key (restrictedFixedMultiplicity K Ω V m G + 1)
    (ENat.lt_add_one_iff hx |>.mpr le_rfl)
  obtain ⟨χ, hχ, hχe⟩ := exists_unit_of_mem_divisorialSections hs h0
  refine ⟨s, hsV, h0, χ, hχ, hχe, le_antisymm
    (restrictedFixedMultiplicity_le_toNat hsV hs h0 hχ G) ?_⟩
  rw [sectionVanishingOrder_eq_of_unit hs hχ G] at hlt
  exact (ENat.lt_add_one_iff hx).mp hlt

/-- **Fixed multiplicities of multiples.** If `V_m V_n ⊆ V_{m+n}`, the sections of `V_m` are
sections of `m K + ⌊mΩ⌋`, and `mΩ` is integral, then `Fix(𝓛_{am}) ≤ a Fix(𝓛_m)` along every prime
divisor. -/
theorem restrictedFixedMultiplicity_mul_le {K : Divisor S} {Ω : QDivisor S}
    {V : ℕ → Submodule R (RationalFunctions S)}
    (hmul : ∀ m n, ∀ s ∈ V m, ∀ t ∈ V n, s * t ∈ V (m + n)) {m a : ℕ}
    (hmem : ∀ s ∈ V m, s ∈ divisorialSections (seriesDivisor K Ω m))
    (hmem' : ∀ s ∈ V (a * m), s ∈ divisorialSections (seriesDivisor K Ω (a * m)))
    (hint : ∀ P : MMP.Mori.PrimeDivisor S, ∃ z : ℤ, (m : ℚ) * Ω.coeff P = z) (ha : 0 < a)
    (G : MMP.Mori.PrimeDivisor S) :
    restrictedFixedMultiplicity K Ω V (a * m) G ≤ a * restrictedFixedMultiplicity K Ω V m G := by
  by_cases hne : ∃ s ∈ V m, s ≠ 0
  · obtain ⟨s, hsV, hs0, χ, hχ, hχe, hfm⟩ := exists_restrictedFixedMultiplicity_eq hmem hne G
    have hsa := pow_mem_of_mul_mem hmul hsV ha
    have hχa : (((χ ^ a : (RationalFunctions S)ˣ)) : RationalFunctions S) = s ^ a := by
      rw [Units.val_pow_eq_pow_val, hχ]
    have h1 := restrictedFixedMultiplicity_le_toNat hsa (hmem' _ hsa)
      (by
        have : Nontrivial (RationalFunctions S) := ⟨⟨s, 0, hs0⟩⟩
        rw [← hχa]; exact (χ ^ a).ne_zero) hχa G
    refine h1.trans ?_
    rw [coeff_seriesDivisor_mul hint a, PrimeDivisor.ord_pow, hfm]
    have hc := hχe G
    have : ((a : ℤ) * (seriesDivisor K Ω m).coeff G + a • G.ord χ).toNat =
        a * ((seriesDivisor K Ω m).coeff G + G.ord χ).toNat := by
      rw [nsmul_eq_mul, ← mul_add, Int.toNat_mul (by positivity) hc]
      simp
    rw [this]
    push_cast
    rfl
  · push Not at hne
    have : restrictedFixedMultiplicity K Ω V m G = ⊤ := by
      unfold restrictedFixedMultiplicity
      refine iInf_eq_top.mpr fun s => iInf_eq_top.mpr fun hsV => iInf_eq_top.mpr fun hs =>
        iInf_eq_top.mpr fun h0 => absurd (hne s hsV) h0
    rw [this]
    have : (a : ℕ∞) ≠ 0 := by exact_mod_cast ha.ne'
    simp [this]

open scoped ENNReal in
/-- The normalized fixed parts decrease along multiples: `F_{am} ≤ F_m`. -/
theorem restrictedNormalizedFixedPart_mul_le {K : Divisor S} {Ω : QDivisor S}
    {V : ℕ → Submodule R (RationalFunctions S)}
    (hmul : ∀ m n, ∀ s ∈ V m, ∀ t ∈ V n, s * t ∈ V (m + n)) {m a : ℕ}
    (hmem : ∀ s ∈ V m, s ∈ divisorialSections (seriesDivisor K Ω m))
    (hmem' : ∀ s ∈ V (a * m), s ∈ divisorialSections (seriesDivisor K Ω (a * m)))
    (hint : ∀ P : MMP.Mori.PrimeDivisor S, ∃ z : ℤ, (m : ℚ) * Ω.coeff P = z) (ha : 0 < a)
    (G : MMP.Mori.PrimeDivisor S) :
    restrictedNormalizedFixedPart K Ω V (a * m) G ≤ restrictedNormalizedFixedPart K Ω V m G := by
  unfold restrictedNormalizedFixedPart
  by_cases hm : m = 0
  · subst hm
    simp
  have h2 : ((restrictedFixedMultiplicity K Ω V (a * m) G : ℕ∞) : ℝ≥0∞) ≤
      (a : ℝ≥0∞) * ((restrictedFixedMultiplicity K Ω V m G : ℕ∞) : ℝ≥0∞) := by
    simpa using ENat.toENNReal_le.mpr (restrictedFixedMultiplicity_mul_le hmul hmem hmem' hint ha G)
  calc ((restrictedFixedMultiplicity K Ω V (a * m) G : ℕ∞) : ℝ≥0∞) / ((a * m : ℕ) : ℝ≥0∞)
      ≤ ((a : ℝ≥0∞) * ((restrictedFixedMultiplicity K Ω V m G : ℕ∞) : ℝ≥0∞)) /
          ((a : ℝ≥0∞) * (m : ℝ≥0∞)) := by
        push_cast
        exact ENNReal.div_le_div_right h2 _
    _ = _ := ENNReal.mul_div_mul_left _ _ (by exact_mod_cast ha.ne') (ENNReal.natCast_ne_top a)

/-- If `V_q` contains a nonzero section, so does `V_m` for every positive multiple `m` of `q`. -/
theorem exists_ne_zero_mem_of_dvd {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule R (RationalFunctions S)}
    (hmul : ∀ m n, ∀ s ∈ V m, ∀ t ∈ V n, s * t ∈ V (m + n))
    (hmem : ∀ s ∈ V q, s ∈ divisorialSections (seriesDivisor K Ω q))
    (hne : ∃ s ∈ V q, s ≠ 0) {m : ℕ} (hqm : q ∣ m) (hm : 0 < m) : ∃ s ∈ V m, s ≠ 0 := by
  obtain ⟨s, hsV, hs0⟩ := hne
  obtain ⟨χ, hχ, -⟩ := exists_unit_of_mem_divisorialSections (hmem s hsV) hs0
  obtain ⟨b, rfl⟩ := hqm
  have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  refine ⟨s ^ b, ?_, ?_⟩
  · have := pow_mem_of_mul_mem hmul hsV hb
    rwa [mul_comm] at this
  · have : Nontrivial (RationalFunctions S) := ⟨⟨s, 0, hs0⟩⟩
    rw [← hχ, ← Units.val_pow_eq_pow_val]
    exact (χ ^ b).ne_zero

/-- The fixed multiplicity of `V_m` vanishes outside a finite set of prime divisors. -/
theorem finite_support_restrictedFixedMultiplicity {K : Divisor S} {Ω : QDivisor S}
    {V : ℕ → Submodule R (RationalFunctions S)} {m : ℕ}
    (hmem : ∀ s ∈ V m, s ∈ divisorialSections (seriesDivisor K Ω m))
    (hne : ∃ s ∈ V m, s ≠ 0) :
    {G : MMP.Mori.PrimeDivisor S | restrictedFixedMultiplicity K Ω V m G ≠ 0}.Finite := by
  classical
  obtain ⟨s, hsV, hs0⟩ := hne
  obtain ⟨χ, hχ, -⟩ := exists_unit_of_mem_divisorialSections (hmem s hsV) hs0
  refine (((seriesDivisor K Ω m).support ∪
    (MMP.Mori.principalDivisor χ).support).finite_toSet).subset fun G hG => ?_
  by_contra hGn
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or,
    not_not] at hGn
  apply hG
  have h1 := restrictedFixedMultiplicity_le_toNat hsV (hmem s hsV) hs0 hχ G
  have h2 : (seriesDivisor K Ω m).coeff G = 0 := hGn.1
  have h3 : G.ord χ = 0 := hGn.2
  rw [h2, h3] at h1
  simpa using h1

end SeriesFixed

section ClippedBoundary

open scoped ENNReal

variable {S : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]

omit [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S] in
/-- The coefficient of `Ω - coeffwiseMin Ω F` along `G` is `Ω_G - min(Ω_G, F G)`. -/
theorem coeff_toRDivisor_sub_coeffwiseMin (Ω : QDivisor S) (F : MMP.Mori.PrimeDivisor S → ℝ≥0∞)
    (G : MMP.Mori.PrimeDivisor S) :
    (QDivisor.toRDivisor Ω - coeffwiseMin Ω F).coeff G =
      (Ω.coeff G : ℝ) - (min (ENNReal.ofReal (Ω.coeff G : ℝ)) (F G)).toReal := by
  rw [DivisorWithCoeffs.coeff_sub, QDivisor.coeff_toRDivisor, coeff_coeffwiseMin]

/-- For `0 ≤ x`, the minimum of `x` and `n / m` computed in `ℝ≥0∞` is `min x (n / m)`. -/
theorem toReal_min_ofReal_natCast_div {x : ℝ} (hx : 0 ≤ x) (n m : ℕ) (hm : 0 < m) :
    (min (ENNReal.ofReal x) ((n : ℝ≥0∞) / (m : ℝ≥0∞))).toReal = min x ((n : ℝ) / m) := by
  have h1 : (n : ℝ≥0∞) / (m : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) / m) := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hm), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  rw [h1]
  rcases le_total x ((n : ℝ) / m) with h | h
  · rw [min_eq_left (ENNReal.ofReal_le_ofReal h), min_eq_left h, ENNReal.toReal_ofReal hx]
  · rw [min_eq_right (ENNReal.ofReal_le_ofReal h), min_eq_right h,
      ENNReal.toReal_ofReal (by positivity)]

/-- For `0 < m` and `m ω = z`, `m (K + (ω - min ω (n / m)) + o / m) = m K + z + o - min z n`. -/
theorem mul_clipped_coeff_eq {m : ℝ} (hm : 0 < m) (ω n K o z : ℝ) (hz : m * ω = z) :
    m * (K + (ω - min ω (n / m)) + (1 / m) * o) = (m * K + z + o) - min z n := by
  have h1 : m * min ω (n / m) = min z n := by
    rw [mul_min_of_nonneg _ _ hm.le, hz]
    congr 1
    field_simp
  have h2 : m * ((1 / m) * o) = o := by field_simp
  rw [mul_add, mul_add, mul_sub, h1, h2, hz]
  ring

variable {R : Type*} [Semiring R] [Module R (RationalFunctions S)]

/-- If the fixed multiplicity of `V m` along `P` is finite, then the coefficient of
`restrictedClippedBoundaryAt K Ω V m` along `P` is `Ω_P - min(Ω_P, mult_P / m)`, where `mult_P` is
`restrictedFixedMultiplicity K Ω V m P`. -/
theorem coeff_restrictedClippedBoundaryAt_of_ne_top {K : Divisor S} {Ω : QDivisor S}
    {V : ℕ → Submodule R (RationalFunctions S)} {m : ℕ} (hm : 0 < m)
    (hΩ0 : ∀ P : MMP.Mori.PrimeDivisor S, 0 ≤ Ω.coeff P) (P : MMP.Mori.PrimeDivisor S)
    (hfin : restrictedFixedMultiplicity K Ω V m P ≠ ⊤) :
    (restrictedClippedBoundaryAt K Ω V m).coeff P =
      (Ω.coeff P : ℝ) - min (Ω.coeff P : ℝ)
        (((restrictedFixedMultiplicity K Ω V m P).toNat : ℝ) / m) := by
  unfold restrictedClippedBoundaryAt
  rw [coeff_toRDivisor_sub_coeffwiseMin]
  unfold restrictedNormalizedFixedPart
  have h1 : ((restrictedFixedMultiplicity K Ω V m P : ℕ∞) : ℝ≥0∞) =
      (((restrictedFixedMultiplicity K Ω V m P).toNat : ℕ) : ℝ≥0∞) := by
    rw [← ENat.toENNReal_coe, ENat.natCast_toNat hfin]
  rw [h1, toReal_min_ofReal_natCast_div (by exact_mod_cast hΩ0 P) _ _ hm]

/-- **No positive component of `Θ_m` is a stable base prime of `K + Θ_m`.** -/
theorem not_isInRelativeDivisorialStableBase_of_pos_coeff_restrictedClippedBoundaryAt
    {T : Scheme.{0}} (f : S ⟶ T) {K : Divisor S} {Ω : QDivisor S}
    {V : ℕ → Submodule R (RationalFunctions S)} {m : ℕ} (hm : 0 < m)
    (hΩ0 : ∀ P : MMP.Mori.PrimeDivisor S, 0 ≤ Ω.coeff P)
    (hmem : ∀ s ∈ V m, s ∈ divisorialSections (seriesDivisor K Ω m))
    (hint : ∀ P : MMP.Mori.PrimeDivisor S, ∃ z : ℤ, (m : ℚ) * Ω.coeff P = z)
    (hne : ∃ s ∈ V m, s ≠ 0) (G : MMP.Mori.PrimeDivisor S)
    (hG : 0 < (restrictedClippedBoundaryAt K Ω V m).coeff G) :
    ¬ IsInRelativeDivisorialStableBase f
      (Divisor.toRDivisor K + restrictedClippedBoundaryAt K Ω V m) G := by
  intro hstab
  obtain ⟨s, hsV, hs0, χ, hχ, hχe, hfmG⟩ := exists_restrictedFixedMultiplicity_eq hmem hne G
  have hle : ∀ P, restrictedFixedMultiplicity K Ω V m P ≤
      (((seriesDivisor K Ω m).coeff P + P.ord χ).toNat : ℕ∞) := fun P =>
    restrictedFixedMultiplicity_le_toNat hsV (hmem s hsV) hs0 hχ P
  have hfin := restrictedFixedMultiplicity_ne_top hmem hne
  choose z hz using hint
  set n : MMP.Mori.PrimeDivisor S → ℕ := fun P => (restrictedFixedMultiplicity K Ω V m P).toNat
    with hn
  have hnle : ∀ P, (n P : ℤ) ≤ (seriesDivisor K Ω m).coeff P + P.ord χ := by
    intro P
    have h1 : n P ≤ ((seriesDivisor K Ω m).coeff P + P.ord χ).toNat := by
      have := hle P
      rw [hn]
      simp only
      exact ENat.toNat_le_of_le_natCast this
    have h2 := hχe P
    omega
  have hcoeffD : ∀ P, (seriesDivisor K Ω m).coeff P = m * K.coeff P + z P := by
    intro P
    rw [coeff_seriesDivisor, hz P, Int.floor_intCast]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- the coefficients of the representative
  set L : RDivisor S := (Divisor.toRDivisor K + restrictedClippedBoundaryAt K Ω V m) +
    ∑ j : Fin 1, (fun _ => (1 / (m : ℝ))) j • Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
      (MMP.Mori.principalDivisor ((fun _ => χ) j)) with hL
  have hLcoeff : ∀ P, L.coeff P = (K.coeff P : ℝ) +
      ((Ω.coeff P : ℝ) - min (Ω.coeff P : ℝ) ((n P : ℝ) / m)) + (1 / (m : ℝ)) * (P.ord χ : ℝ) := by
    intro P
    rw [hL, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
      coeff_restrictedClippedBoundaryAt_of_ne_top hm hΩ0 P (hfin P)]
    simp [DivisorWithCoeffs.coeff_apply, MMP.Mori.principalDivisor]
    rfl
  have hzR : ∀ P, (m : ℝ) * (Ω.coeff P : ℝ) = z P := fun P => by exact_mod_cast hz P
  have hkey : ∀ P, (m : ℝ) * L.coeff P =
      (((seriesDivisor K Ω m).coeff P + P.ord χ : ℤ) : ℝ) - min (z P : ℝ) (n P) := by
    intro P
    rw [hLcoeff, mul_clipped_coeff_eq hmR _ _ _ _ _ (hzR P), hcoeffD P]
    push_cast
    ring
  have hLeff : IsEffectiveOn L (f ⁻¹ᵁ ⊤) := by
    intro P _
    refine (mul_nonneg_iff_of_pos_left hmR).mp ?_
    rw [hkey P]
    have h1 : (n P : ℝ) ≤ (((seriesDivisor K Ω m).coeff P + P.ord χ : ℤ) : ℝ) := by
      exact_mod_cast hnle P
    linarith [min_le_right (z P : ℝ) (n P)]
  have hpos := hstab ⊤ trivial 1 (fun _ => 1 / (m : ℝ)) (fun _ => χ) hLeff
  -- along `G` the representative has coefficient zero
  have hnG : (n G : ℤ) = (seriesDivisor K Ω m).coeff G + G.ord χ := by
    have h1 : n G = ((seriesDivisor K Ω m).coeff G + G.ord χ).toNat := by
      rw [hn]
      simp only
      rw [hfmG]
      simp
    have h2 := hχe G
    omega
  have hzG : (n G : ℝ) < z G := by
    rw [coeff_restrictedClippedBoundaryAt_of_ne_top hm hΩ0 G (hfin G)] at hG
    have h1 : min (Ω.coeff G : ℝ) ((n G : ℝ) / m) < Ω.coeff G := by linarith
    rcases min_lt_iff.mp h1 with h | h
    · exact (lt_irrefl _ h).elim
    · have := (div_lt_iff₀ hmR).mp h
      rw [← hzR G]
      linarith
  have h0 : (m : ℝ) * L.coeff G = 0 := by
    rw [hkey G, min_eq_right hzG.le, ← hnG]
    simp
  have hL0 : L.coeff G = 0 := (mul_eq_zero.mp h0).resolve_left hmR.ne'
  exact absurd hpos (by
    rw [hL0]
    exact lt_irrefl _)

/-- If every fixed multiplicity of `V_m` is finite, the clipped boundary `Θ_m` is rational: it is
`Ω - Δ` for a `ℚ`-divisor `Δ` with `0 ≤ Δ ≤ Ω`. -/
theorem exists_restrictedClippedBoundaryAt_eq_toRDivisor_sub {K : Divisor S} {Ω : QDivisor S}
    {V : ℕ → Submodule R (RationalFunctions S)} {m : ℕ} (hm : 0 < m)
    (hΩ0 : ∀ P : MMP.Mori.PrimeDivisor S, 0 ≤ Ω.coeff P)
    (hfin : ∀ P, restrictedFixedMultiplicity K Ω V m P ≠ ⊤) :
    ∃ Δ : QDivisor S, (∀ P, 0 ≤ Δ.coeff P) ∧ (∀ P, Δ.coeff P ≤ Ω.coeff P) ∧
      restrictedClippedBoundaryAt K Ω V m = QDivisor.toRDivisor (Ω - Δ) := by
  classical
  let f : MMP.Mori.PrimeDivisor S → ℚ := fun P =>
    min (Ω.coeff P) (((restrictedFixedMultiplicity K Ω V m P).toNat : ℚ) / m)
  have hf : ∀ P, f P ≠ 0 → P ∈ Ω.support := by
    intro P hP
    rw [Finsupp.mem_support_iff]
    intro h0
    apply hP
    have : Ω.coeff P = 0 := h0
    simp only [f, this]
    exact min_eq_left (by positivity)
  let Δ : QDivisor S := Finsupp.onFinset Ω.support f hf
  have hΔ : ∀ P, Δ.coeff P = f P := fun P => rfl
  refine ⟨Δ, fun P => ?_, fun P => ?_, ?_⟩
  · rw [hΔ]
    exact le_min (hΩ0 P) (by positivity)
  · rw [hΔ]
    exact min_le_left _ _
  · ext P
    rw [coeff_restrictedClippedBoundaryAt_of_ne_top hm hΩ0 P (hfin P)]
    change _ = ((Ω.coeff P - Δ.coeff P : ℚ) : ℝ)
    rw [hΔ]
    simp only [f]
    push_cast
    rfl

/-- `x - min(x, F)` is antitone in `F : ℝ≥0∞`. -/
theorem clip_antitone {x : ℝ} {F F' : ℝ≥0∞} (h : F ≤ F') :
    x - (min (ENNReal.ofReal x) F').toReal ≤ x - (min (ENNReal.ofReal x) F).toReal := by
  have := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _))
    (min_le_min_left (ENNReal.ofReal x) h)
  linarith

/-- For `0 ≤ x`, `x - min(x, F)` is nonnegative. -/
theorem clip_nonneg {x : ℝ} (hx : 0 ≤ x) (F : ℝ≥0∞) :
    0 ≤ x - (min (ENNReal.ofReal x) F).toReal := by
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_left (ENNReal.ofReal x) F)
  rw [ENNReal.toReal_ofReal hx] at this
  linarith

/-- If `Fn` tends to `F` in `ℝ≥0∞`, then `x - min(x, Fn n)` tends to `x - min(x, F)`. -/
theorem tendsto_clip (x : ℝ) {Fn : ℕ → ℝ≥0∞} {F : ℝ≥0∞}
    (h : Filter.Tendsto Fn Filter.atTop (nhds F)) :
    Filter.Tendsto (fun n => x - (min (ENNReal.ofReal x) (Fn n)).toReal) Filter.atTop
      (nhds (x - (min (ENNReal.ofReal x) F).toReal)) :=
  tendsto_const_nhds.sub ((ENNReal.tendsto_toReal
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _))).comp
      (tendsto_const_nhds.min h))

end ClippedBoundary

section Monotone

open scoped ENNReal Topology
open Filter

variable {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
  [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  {R' : Type*} [Semiring R'] [Module R' (RationalFunctions S)]
  {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
  {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
  {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}

namespace IsGradedRestrictedSeries

/-- The boundary `Ω` of a graded restricted series is effective. -/
theorem coeff_nonneg (h : IsGradedRestrictedSeries sS sT g f d K Ω q V)
    (P : MMP.Mori.PrimeDivisor S) : 0 ≤ Ω.coeff P :=
  h.isKltPair.1.nonneg P

/-- `mΩ` has integral coefficients for `q ∣ m`. -/
theorem exists_int_eq_mul_coeff (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) {m : ℕ}
    (hm : q ∣ m) (P : MMP.Mori.PrimeDivisor S) : ∃ z : ℤ, (m : ℚ) * Ω.coeff P = z :=
  exists_int_eq_mul_coeff_of_isCartierDivisor h.isCartierDivisor_smul hm P

/-- Sections of `V_m` are sections of `m K + ⌊mΩ⌋`. -/
theorem mem_divisorialSections' (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) {m : ℕ}
    (hm : q ∣ m) {s : RationalFunctions S} (hs : s ∈ V m) :
    s ∈ divisorialSections (seriesDivisor K Ω m) :=
  h.mem_divisorialSections m hm s hs

/-- `V_m ≠ 0` for every positive `m` divisible by `q`. -/
theorem exists_ne_zero_mem (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) {m : ℕ}
    (hqm : q ∣ m) (hm : 0 < m) : ∃ s ∈ V m, s ≠ 0 :=
  exists_ne_zero_mem_of_dvd h.mul_mem (fun _ hs => h.mem_divisorialSections' dvd_rfl hs)
    ((Submodule.ne_bot_iff _).1 h.ne_bot) hqm hm

end IsGradedRestrictedSeries

/-- `F_{am} ≤ F_m` for `q ∣ m`. -/
theorem restrictedNormalizedFixedPart_mul_le_of_dvd
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) {m a : ℕ} (hqm : q ∣ m) (ha : 0 < a)
    (G : MMP.Mori.PrimeDivisor S) :
    restrictedNormalizedFixedPart K Ω V (a * m) G ≤ restrictedNormalizedFixedPart K Ω V m G :=
  restrictedNormalizedFixedPart_mul_le h.mul_mem (fun _ hs => h.mem_divisorialSections' hqm hs)
    (fun _ hs => h.mem_divisorialSections' (dvd_mul_of_dvd_right hqm a) hs)
    (h.exists_int_eq_mul_coeff hqm) ha G

/-- **The factorial fixed parts decrease**: `F_{q (n+1)!} ≤ F_{q n!}`. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem restrictedNormalizedFixedPart_factorial_succ_le
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) (n : ℕ) (G : MMP.Mori.PrimeDivisor S) :
    restrictedNormalizedFixedPart K Ω V (q * (n + 1).factorial) G ≤
      restrictedNormalizedFixedPart K Ω V (q * n.factorial) G := by
  have := restrictedNormalizedFixedPart_mul_le_of_dvd h (m := q * n.factorial) (a := n + 1)
    (dvd_mul_right _ _) (Nat.succ_pos n) G
  rwa [show (n + 1) * (q * n.factorial) = q * (n + 1).factorial by
    rw [Nat.factorial_succ]; ring] at this

/-- **Every admissible `F_m` is at least `F`.** -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem restrictedAsymptoticFixedPart_le_normalizedFixedPart
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) {m : ℕ} (hm : 0 < m) (hqm : q ∣ m)
    (G : MMP.Mori.PrimeDivisor S) :
    restrictedAsymptoticFixedPart K Ω q V G ≤ restrictedNormalizedFixedPart K Ω V m G := by
  obtain ⟨k, rfl⟩ := hqm
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have h1 := restrictedNormalizedFixedPart_mul_le_of_dvd h (m := q * k) (a := (k - 1).factorial)
    (dvd_mul_right _ _) (Nat.factorial_pos _) G
  rw [show (k - 1).factorial * (q * k) = q * k.factorial by
    rw [← Nat.mul_factorial_pred hk.ne']; ring] at h1
  exact (iInf_le_of_le k (iInf_le_of_le hk le_rfl)).trans h1

/-- The factorial fixed parts converge to `F = inf_{n ≥ 1} F_{q n!}`. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem tendsto_restrictedNormalizedFixedPart_factorial
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) (G : MMP.Mori.PrimeDivisor S) :
    Tendsto (fun n : ℕ => restrictedNormalizedFixedPart K Ω V (q * n.factorial) G) atTop
      (𝓝 (restrictedAsymptoticFixedPart K Ω q V G)) := by
  have hanti : Antitone (fun n : ℕ => restrictedNormalizedFixedPart K Ω V (q * n.factorial) G) :=
    antitone_nat_of_succ_le fun n => restrictedNormalizedFixedPart_factorial_succ_le h n G
  have := tendsto_atTop_iInf hanti
  convert this using 2
  unfold restrictedAsymptoticFixedPart
  refine le_antisymm (le_iInf fun n => ?_) (iInf_mono fun n => le_iInf fun _ => le_rfl)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact iInf_le_of_le 1 (iInf_le_of_le le_rfl (by simp))
  · exact iInf_le_of_le n (iInf_le_of_le hn le_rfl)

/-- The limit `F` is a finite real number along every prime divisor. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem restrictedAsymptoticFixedPart_ne_top
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) (G : MMP.Mori.PrimeDivisor S) :
    restrictedAsymptoticFixedPart K Ω q V G ≠ ⊤ := by
  have hq := h.q_pos
  have h1 := restrictedAsymptoticFixedPart_le_normalizedFixedPart h hq (dvd_refl q) G
  refine ne_top_of_le_ne_top ?_ h1
  unfold restrictedNormalizedFixedPart
  exact (ENNReal.div_lt_top (by
    exact_mod_cast restrictedFixedMultiplicity_ne_top
      (fun _ hs => h.mem_divisorialSections' dvd_rfl hs) (h.exists_ne_zero_mem dvd_rfl hq) G)
    (by exact_mod_cast hq.ne')).ne

/-- The limit `F` has finite support. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem finite_support_restrictedAsymptoticFixedPart
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) :
    {G : MMP.Mori.PrimeDivisor S | restrictedAsymptoticFixedPart K Ω q V G ≠ 0}.Finite := by
  have hq := h.q_pos
  refine (finite_support_restrictedFixedMultiplicity
    (fun _ hs => h.mem_divisorialSections' dvd_rfl hs) (h.exists_ne_zero_mem dvd_rfl hq)).subset
    fun G hG => ?_
  intro h0
  apply hG
  have h1 := restrictedAsymptoticFixedPart_le_normalizedFixedPart h hq (dvd_refl q) G
  unfold restrictedNormalizedFixedPart at h1
  rw [h0] at h1
  simpa using h1

/-- The coefficient of `restrictedClippedBoundary K Ω q V` along `G` is `Ω_G - min(Ω_G, F G)`,
where `F` is `restrictedAsymptoticFixedPart K Ω q V`. -/
theorem coeff_restrictedClippedBoundary (K : Divisor S) (Ω : QDivisor S) (q : ℕ)
    (V : ℕ → Submodule R' (RationalFunctions S)) (G : MMP.Mori.PrimeDivisor S) :
    (restrictedClippedBoundary K Ω q V).coeff G = (Ω.coeff G : ℝ) -
      (min (ENNReal.ofReal (Ω.coeff G : ℝ)) (restrictedAsymptoticFixedPart K Ω q V G)).toReal :=
  coeff_toRDivisor_sub_coeffwiseMin _ _ _

/-- The coefficient of `restrictedClippedBoundaryAt K Ω V m` along `G` is `Ω_G - min(Ω_G, F G)`,
where `F` is `restrictedNormalizedFixedPart K Ω V m`. -/
theorem coeff_restrictedClippedBoundaryAt (K : Divisor S) (Ω : QDivisor S)
    (V : ℕ → Submodule R' (RationalFunctions S)) (m : ℕ) (G : MMP.Mori.PrimeDivisor S) :
    (restrictedClippedBoundaryAt K Ω V m).coeff G = (Ω.coeff G : ℝ) -
      (min (ENNReal.ofReal (Ω.coeff G : ℝ)) (restrictedNormalizedFixedPart K Ω V m G)).toReal :=
  coeff_toRDivisor_sub_coeffwiseMin _ _ _

/-- `Θ_{q n!} ≤ Θ_{q (n+1)!}`: the clipped boundaries increase. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem restrictedClippedBoundaryAt_factorial_le_succ
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) (n : ℕ) :
    restrictedClippedBoundaryAt K Ω V (q * n.factorial) ≤
      restrictedClippedBoundaryAt K Ω V (q * (n + 1).factorial) :=
  Finsupp.le_def.mpr fun G => by
    change (restrictedClippedBoundaryAt K Ω V (q * n.factorial)).coeff G ≤
      (restrictedClippedBoundaryAt K Ω V (q * (n + 1).factorial)).coeff G
    rw [coeff_restrictedClippedBoundaryAt, coeff_restrictedClippedBoundaryAt]
    exact clip_antitone (restrictedNormalizedFixedPart_factorial_succ_le h n G)

/-- `Θ_m ≤ Θ` for every admissible `m`. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem restrictedClippedBoundaryAt_le_restrictedClippedBoundary
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) {m : ℕ} (hm : 0 < m) (hqm : q ∣ m) :
    restrictedClippedBoundaryAt K Ω V m ≤ restrictedClippedBoundary K Ω q V :=
  Finsupp.le_def.mpr fun G => by
    change (restrictedClippedBoundaryAt K Ω V m).coeff G ≤
      (restrictedClippedBoundary K Ω q V).coeff G
    rw [coeff_restrictedClippedBoundaryAt, coeff_restrictedClippedBoundary]
    exact clip_antitone (restrictedAsymptoticFixedPart_le_normalizedFixedPart h hm hqm G)

/-- `0 ≤ Θ_m`: the clipped boundary is effective. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem zero_le_restrictedClippedBoundaryAt
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) (m : ℕ) :
    0 ≤ restrictedClippedBoundaryAt K Ω V m :=
  Finsupp.le_def.mpr fun G => by
    change (0 : ℝ) ≤ (restrictedClippedBoundaryAt K Ω V m).coeff G
    rw [coeff_restrictedClippedBoundaryAt]
    exact clip_nonneg (by exact_mod_cast h.coeff_nonneg G) _

/-- `Θ_m ≤ Ω`. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem restrictedClippedBoundaryAt_le (m : ℕ) :
    restrictedClippedBoundaryAt K Ω V m ≤ QDivisor.toRDivisor Ω :=
  Finsupp.le_def.mpr fun G => by
    change (restrictedClippedBoundaryAt K Ω V m).coeff G ≤ (Ω.coeff G : ℝ)
    rw [coeff_restrictedClippedBoundaryAt]
    exact sub_le_self _ ENNReal.toReal_nonneg

/-- `0 ≤ Θ`: the asymptotic clipped boundary is effective. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem zero_le_restrictedClippedBoundary
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) :
    0 ≤ restrictedClippedBoundary K Ω q V :=
  Finsupp.le_def.mpr fun G => by
    change (0 : ℝ) ≤ (restrictedClippedBoundary K Ω q V).coeff G
    rw [coeff_restrictedClippedBoundary]
    exact clip_nonneg (by exact_mod_cast h.coeff_nonneg G) _

/-- `Θ ≤ Ω`. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem restrictedClippedBoundary_le :
    restrictedClippedBoundary K Ω q V ≤ QDivisor.toRDivisor Ω :=
  Finsupp.le_def.mpr fun G => by
    change (restrictedClippedBoundary K Ω q V).coeff G ≤ (Ω.coeff G : ℝ)
    rw [coeff_restrictedClippedBoundary]
    exact sub_le_self _ ENNReal.toReal_nonneg

/-- **The clipped boundaries `Θ_{q n!}` increase to `Θ`**, coefficientwise. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem tendsto_restrictedClippedBoundaryAt_factorial
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) (G : MMP.Mori.PrimeDivisor S) :
    Tendsto (fun n : ℕ => (restrictedClippedBoundaryAt K Ω V (q * n.factorial)).coeff G) atTop
      (𝓝 ((restrictedClippedBoundary K Ω q V).coeff G)) := by
  simp only [coeff_restrictedClippedBoundaryAt, coeff_restrictedClippedBoundary]
  exact tendsto_clip _ (tendsto_restrictedNormalizedFixedPart_factorial h G)

/-- `Θ_m` is supported on `Supp Θ`. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem support_restrictedClippedBoundaryAt_subset
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) {m : ℕ} (hm : 0 < m) (hqm : q ∣ m) :
    (restrictedClippedBoundaryAt K Ω V m).support ⊆
      (restrictedClippedBoundary K Ω q V).support := by
  intro G hG
  rw [Finsupp.mem_support_iff] at hG ⊢
  intro h0
  apply hG
  have h1 := Finsupp.le_def.mp (restrictedClippedBoundaryAt_le_restrictedClippedBoundary h hm hqm) G
  have h2 := Finsupp.le_def.mp (zero_le_restrictedClippedBoundaryAt h m) G
  change (restrictedClippedBoundaryAt K Ω V m).coeff G ≤
    (restrictedClippedBoundary K Ω q V).coeff G at h1
  change (0 : ℝ) ≤ (restrictedClippedBoundaryAt K Ω V m).coeff G at h2
  have h3 : (restrictedClippedBoundary K Ω q V).coeff G = 0 := h0
  exact le_antisymm (h3 ▸ h1) h2

/-- For admissible `m`, `Θ_m` is rational and klt: it is `B` for a `ℚ`-divisor `B` with `(S, B)`
klt. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem exists_isKltPair_restrictedClippedBoundaryAt
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) {m : ℕ} (hm : 0 < m) (hqm : q ∣ m) :
    ∃ B : QDivisor S, QDivisor.toRDivisor B = restrictedClippedBoundaryAt K Ω V m ∧
      IsKltPair sS B := by
  obtain ⟨Δ, hΔ0, hΔΩ, hΔ⟩ := exists_restrictedClippedBoundaryAt_eq_toRDivisor_sub (K := K) (V := V) hm
    h.coeff_nonneg (fun P => restrictedFixedMultiplicity_ne_top
      (fun _ hs => h.mem_divisorialSections' hqm hs) (h.exists_ne_zero_mem hqm hm) P)
  exact ⟨Ω - Δ, hΔ.symm, isKltPair_sub_of_isSmoothScheme h.isSmoothScheme h.isKltPair hΔ0 hΔΩ⟩

/-- **No component of `Θ_m` is a stable base prime of `K_S + Θ_m`**, relative to `T`. -/
@[mmp "lem_fourfold_restricted_fixed_parts_monotone"]
theorem not_isInRelativeDivisorialStableBase_restrictedClippedBoundaryAt
    (h : IsGradedRestrictedSeries sS sT g f d K Ω q V) {m : ℕ} (hm : 0 < m) (hqm : q ∣ m)
    (G : MMP.Mori.PrimeDivisor S) (hG : 0 < (restrictedClippedBoundaryAt K Ω V m).coeff G) :
    ¬ IsInRelativeDivisorialStableBase f
      (Divisor.toRDivisor K + restrictedClippedBoundaryAt K Ω V m) G :=
  not_isInRelativeDivisorialStableBase_of_pos_coeff_restrictedClippedBoundaryAt f hm h.coeff_nonneg
    (fun _ hs => h.mem_divisorialSections' hqm hs) (h.exists_int_eq_mul_coeff hqm)
    (h.exists_ne_zero_mem hqm hm) G hG

end Monotone

end MMP.Fourfold
