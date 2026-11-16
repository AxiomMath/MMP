module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.CoverDatum
public import MMP.AlgebraicGeometry.Singularities.Snc.SncOfRelativeSnc
public import MMP.AlgebraicGeometry.Divisor.CoveringTrick.SncDivisibleCover
public import MMP.AlgebraicGeometry.Divisor.CoveringTrick.EtaleRootCover
public import MMP.AlgebraicGeometry.Singularities.Snc.WeakChartEtalePullback
public import MMP.AlgebraicGeometry.Divisor.CartierPullbackSupport
public import MMP.AlgebraicGeometry.Singularities.Snc.ReducedPreimageFiniteCover
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain

/-!
# The cover for the fractional logarithmic complex exists

Let `π : V ⟶ Spec ℂ` be an integral smooth projective variety of dimension `n`, `D = S + Supp Bn`
a relative snc divisor with `S` reduced and `0 ≤ Bn < N`, and `ψ` a rational function with
`N M = Bn + div ψ`. This file proves `MMP.FourfoldProofs.FractionalLogComplexProof.CoverDatum`: there
is a finite surjective `g : V' ⟶ V` from an integral smooth projective variety of dimension `n`
on which the reduced inverse image `S'` of `S` is a relative snc divisor and `g^*ψ` has an `N`-th
root in the function field.

The cover is built in two steps, as in the covering trick [KollarMori, 2.67].

* The components of `D` form an snc divisor. Bloch–Gieseker covers followed by cyclic covers
  clear the components of `Supp Bn` to order `2N`
  (`MMP.FourfoldProofs.FractionalLogComplexProof.exists_cover_clearing`), giving `g₁ : Y₁ ⟶ V` with
  `g₁^*P = 2N G_P` for `P ∈ Supp Bn` and `g₁^*P = G_P` for the other components, the `G_P` reduced
  with snc sum. Then `g₁^* Bn = 2N B₁`, and pulling back `div ψ = N M - Bn` gives
  `div(g₁^*ψ) = N A` with `A = g₁^*M - 2B₁`.
* The divisorial cyclic cover of `(-A, N, g₁^*ψ)` is finite étale; any of its connected components
  `g₂ : V' ⟶ Y₁` carries an `N`-th root of `g₁^*ψ`
  (`MMP.FourfoldProofs.FractionalLogComplexProof.exists_etale_cover_pow_eq_functionFieldMap`).

The components of `S` pull back to the `G_P`, so `g₁⁻¹(Supp S)` is the support of an snc divisor,
with weak charts around every closed point; these pull back along the étale `g₂`, and make the
reduced inverse image of `S` under `g = g₂ ≫ g₁` a relative snc divisor
(`MMP.FourfoldProofs.FractionalLogComplexProof.exists_isRelativeSNC_reducedPreimage`).

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_coverDatum`: the cover exists.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.67
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology MMP.Mori MMP.Mori.Divisor.LogSpreadingProof
open MMP.Threefold.Resolution (map_componentGenericPoint_notMem_supp_of_isDominant')

/-- If each prime divisor `P ∈ A` pulls back along `g` to `E P`, then `∑ P ∈ A, c P • P` pulls back
to `∑ P ∈ A, c P • E P`. -/
theorem isPullback_sum_zsmul_single {X Y : Scheme.{u}} [IrreducibleSpace Y] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] (g : Y ⟶ X) [IsDominant g]
    (hcart : ∀ B : Divisor X, B.IsCartier) (A : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℤ) (E : MMP.Mori.PrimeDivisor X → Divisor Y)
    (h : ∀ P ∈ A, Divisor.IsPullback g (Finsupp.single P (1 : ℤ))
      (map_componentGenericPoint_notMem_supp_of_isDominant' g _) (E P)) :
    Divisor.IsPullback g (∑ P ∈ A, c P • Finsupp.single P (1 : ℤ))
      (map_componentGenericPoint_notMem_supp_of_isDominant' g _) (∑ P ∈ A, c P • E P) := by
  classical
  induction A using Finset.induction_on with
  | empty => exact Divisor.isPullback_zero _
  | insert P A hPA ih =>
    simp only [Finset.sum_insert hPA]
    exact Divisor.IsPullback.add (hcart _) (hcart _) _
      ((h P (Finset.mem_insert_self P A)).zsmul (hcart _) (c P)
        (map_componentGenericPoint_notMem_supp_of_isDominant' g _))
      (ih fun Q hQ => h Q (Finset.mem_insert_of_mem hQ))

open Classical in
/-- **The cover for the fractional logarithmic complex exists** [KollarMori, 2.67]: for a smooth
projective complex variety `V` with relative snc divisor `D = S + Supp Bn`, `S` effective and
`N • M = Bn + div ψ`, there is a finite surjective cover `g : V' ⟶ V` by a smooth projective variety
of dimension `n` on which the reduced inverse image of `S` is relative snc and `g^*ψ` has an `N`-th
root (`CoverDatum n π S N ψ`). -/
theorem exists_coverDatum (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] (hπ : IsProjective π) [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S Bn : MMP.Mori.Divisor V)
    (hS : 0 ≤ S) (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1)
    (N : ℕ) (hN : 0 < N)
    (M : MMP.Mori.Divisor V) (ψ : (MMP.Mori.RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ) :
    CoverDatum n π S N ψ := by
  -- `V` is a smooth projective variety, on which every divisor is Cartier
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  have : IsProper π := hπ.isProper
  have hvarV : AlgebraicGeometry.IsVariety ℂ π := ⟨⟩
  have : AlgebraicGeometry.IsProjectiveVariety ℂ π :=
    (AlgebraicGeometry.isProjectiveVariety_iff_isProjective' ℂ π).2 ⟨hvarV, hπ⟩
  have hcartV : ∀ B : Divisor V, B.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme ((isSmoothScheme_iff π).2 inferInstance)
  -- the coefficients of `D`, `S` and `Bn`
  have hD01 : ∀ E, D E = 0 ∨ D E = 1 := fun E => by
    by_cases h : E ∈ D.support
    · exact Or.inr (hD.1 E h)
    · exact Or.inl (Finsupp.notMem_support_iff.mp h)
  have hSnn : ∀ E, 0 ≤ S E := fun E => hS E
  have hBnS : ∀ E, Bn E ≠ 0 → S E = 0 := fun E h => by
    have := hSB E
    simp only [h, ↓reduceIte] at this
    rcases hD01 E with h0 | h1 <;> have := hSnn E <;> omega
  have hTD : Bn.support ⊆ D.support := fun E hE => by
    rw [Finsupp.mem_support_iff] at hE ⊢
    rw [hSB E]
    simp only [hE, ↓reduceIte]
    have := hSnn E
    omega
  have hSD : S.support ⊆ D.support := fun E hE => by
    rw [Finsupp.mem_support_iff] at hE ⊢
    rw [hSB E]
    have := hSnn E
    split_ifs <;> omega
  have hSBn : ∀ E ∈ S.support, E ∉ Bn.support := fun E hE hEB =>
    Finsupp.mem_support_iff.mp hE (hBnS E (Finsupp.mem_support_iff.mp hEB))
  have hsnc : DivisorWithCoeffs.IsSNC π (∑ P ∈ D.support, Finsupp.single P (1 : ℤ)) := by
    rw [sum_single_one_support_eq D hD01]
    exact isSNC_of_isRelativeSNC π D hD
  -- the cover clearing the components of `Supp Bn` to order `2N`
  obtain ⟨Y₁, g₁, _, _, hproj₁, hsm₁, _, _, _, G, hgen, hpb, hred, hdisj, -, hsnc₁⟩ :=
    exists_cover_clearing ℂ (2 * N) (by omega) π D.support Bn.support hTD
      hsnc
  have : AlgebraicGeometry.IsProjectiveVariety ℂ (g₁ ≫ π) := hproj₁
  have : Smooth (g₁ ≫ π) := hsm₁
  have : IsIntegral Y₁ := hproj₁.toIsIntegral
  have hcart₁ : ∀ B : Divisor Y₁, B.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme ((isSmoothScheme_iff _).2 hsm₁)
  have hpb' : ∀ P ∈ D.support, Divisor.IsPullback g₁ (Finsupp.single P (1 : ℤ))
      (map_componentGenericPoint_notMem_supp_of_isDominant' g₁ _)
      ((if P ∈ Bn.support then ((2 * N : ℕ) : ℤ) else 1) • G P) := fun P hP => hpb P hP
  -- `g₁^* Bn = 2N B₁`
  set B₁ : Divisor Y₁ := ∑ P ∈ Bn.support, Bn P • G P with hB₁def
  have hBnsum : Bn = ∑ P ∈ Bn.support, Bn P • Finsupp.single P (1 : ℤ) := by
    conv_lhs => rw [← Finsupp.sum_single Bn]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finsupp.smul_single_one]
  have hBnpb : Divisor.IsPullback g₁ Bn
      (map_componentGenericPoint_notMem_supp_of_isDominant' g₁ _)
      (((2 * N : ℕ) : ℤ) • B₁) := by
    have h := isPullback_sum_zsmul_single g₁ hcartV Bn.support Bn
      (fun P => ((2 * N : ℕ) : ℤ) • G P) (fun P hP => by
        have := hpb' P (hTD hP)
        simpa only [hP, ↓reduceIte] using this)
    rw [← hBnsum] at h
    have e : ∑ P ∈ Bn.support, Bn P • ((2 * N : ℕ) : ℤ) • G P = ((2 * N : ℕ) : ℤ) • B₁ := by
      rw [hB₁def, Finset.smul_sum]
      exact Finset.sum_congr rfl fun P _ => smul_comm _ _ _
    rwa [e] at h
  -- `div(g₁^*ψ) = N A` with `A = g₁^*M - 2 B₁`
  set M₁ := Divisor.pullback (f := g₁) M (hcartV M)
    (map_componentGenericPoint_notMem_supp_of_isDominant' g₁ _)
  have hMpb : Divisor.IsPullback g₁ M (map_componentGenericPoint_notMem_supp_of_isDominant' g₁ _)
      M₁ := Divisor.isPullback_pullback (hcartV M) _
  have hψgen := map_componentGenericPoint_notMem_supp_of_isDominant' g₁ (principalDivisor ψ)
  set ψ₁ := pullbackRationalFunction g₁ ψ hψgen
  have hψpb := Divisor.isPullback_principalDivisor (f := g₁) ψ hψgen
  have hdivψ : principalDivisor ψ = (N : ℤ) • M + (-1 : ℤ) • Bn := by
    rw [hψ]; abel
  have h2 : Divisor.IsPullback g₁ (principalDivisor ψ) hψgen
      ((N : ℤ) • M₁ + (-1 : ℤ) • (((2 * N : ℕ) : ℤ) • B₁)) := by
    refine Divisor.IsPullback.of_eq
      (hB₁ := map_componentGenericPoint_notMem_supp_of_isDominant' g₁ _) hdivψ.symm ?_
    exact Divisor.IsPullback.add (hcartV _) (hcartV _) _
      (hMpb.zsmul (hcartV _) N (map_componentGenericPoint_notMem_supp_of_isDominant' g₁ _))
      (hBnpb.zsmul (hcartV _) (-1) (map_componentGenericPoint_notMem_supp_of_isDominant' g₁ _))
  set A : Divisor Y₁ := M₁ - (2 : ℤ) • B₁ with hAdef
  have hA : principalDivisor ψ₁ = N • A := by
    rw [hψpb.eq (hcartV _) h2, hAdef]
    push_cast
    module
  -- the étale cover extracting an `N`-th root of `g₁^*ψ`
  have : NeZero N := ⟨by omega⟩
  obtain ⟨Y₂, g₂, _, _, _, _, z, hz⟩ :=
    exists_etale_cover_pow_eq_functionFieldMap (g₁ ≫ π) N A (hcart₁ A) ψ₁ hA
  -- the composite cover `g = g₂ ≫ g₁`
  have hsm : Smooth ((g₂ ≫ g₁) ≫ π) := by rw [Category.assoc]; infer_instance
  have hvar : AlgebraicGeometry.IsVariety ℂ ((g₂ ≫ g₁) ≫ π) := ⟨⟩
  have hproj : MMP.Mori.IsProjectiveVariety ℂ ((g₂ ≫ g₁) ≫ π) :=
    isProjectiveVariety_comp_of_isFinite π (g₂ ≫ g₁) hvar
  have : MMP.Mori.IsVariety ℂ ((g₂ ≫ g₁) ≫ π) := hvar
  have hrel : SmoothOfRelativeDimension n ((g₂ ≫ g₁) ≫ π) :=
    smoothOfRelativeDimension_comp_of_isFinite π n (g₂ ≫ g₁)
  have : MMP.Mori.IsVariety ℂ (g₁ ≫ π) := hproj₁.toIsVariety
  have : SmoothOfRelativeDimension n (g₁ ≫ π) := smoothOfRelativeDimension_comp_of_isFinite π n g₁
  have : IsLocallyNoetherian Y₂ := LocallyOfFiniteType.isLocallyNoetherian ((g₂ ≫ g₁) ≫ π)
  have : IsNormal Y₂ := isNormal_of_smooth_over_field ((g₂ ≫ g₁) ≫ π)
  have : CompactSpace Y₂ := QuasiCompact.compactSpace_of_compactSpace ((g₂ ≫ g₁) ≫ π)
  -- the pull-back of `S` to `Y₁` is the snc divisor `∑_{P ∈ S} G_P`, of support `g₁⁻¹(Supp S)`
  set Ssum : Divisor Y₁ := ∑ P ∈ S.support, G P with hSsumdef
  have hGnn : ∀ P ∈ D.support, 0 ≤ G P := fun P hP Q => by
    rcases (hred P hP).2 Q with h | h <;> simp [h]
  have hsncS : DivisorWithCoeffs.IsSNC (g₁ ≫ π) Ssum := by
    refine hsnc₁.of_support_subset fun Q hQ => ?_
    obtain ⟨P, hP, hQP⟩ := (mem_support_sum_iff _ G (fun P hP => hGnn P (hSD hP)) Q).1 hQ
    exact (mem_support_sum_iff _ G hGnn Q).2 ⟨P, hSD hP, hQP⟩
  have hSpb : Divisor.IsPullback g₁ (∑ P ∈ S.support, Finsupp.single P (1 : ℤ))
      (map_componentGenericPoint_notMem_supp_of_isDominant' g₁ _) Ssum :=
    divisor_isPullback_sum_single g₁ hcartV S.support G (fun P hP => by
      have := hpb' P (hSD hP)
      simpa only [hSBn P hP, ↓reduceIte, one_smul] using this)
  have hSsupp : (∑ P ∈ S.support, Finsupp.single P (1 : ℤ) : Divisor V).support = S.support := by
    ext P
    rw [Finsupp.mem_support_iff, sum_single_one_apply]
    split_ifs with h <;> simp [h]
  have hZ₁ : (Ssum.supp : Set Y₁) =
      g₁ ⁻¹' (⋃ E ∈ S.support, AlgebraicGeometry.PrimeDivisor.support E) := by
    rw [coe_supp_eq_preimage_of_isPullback g₁ (hcartV _) (fun Q => by
      rw [sum_single_one_apply]; split_ifs <;> simp) hSpb, coe_supp_eq_biUnion, hSsupp]
  -- weak charts of `g⁻¹(Supp S)` around every point of `Y₂`
  have : JacobsonSpace Y₁ := LocallyOfFiniteType.jacobsonSpace (g₁ ≫ π)
  have hchart : ∀ y : Y₂, ∃ c : WeakChart ((g₂ ≫ g₁) ≫ π) n ((g₂ ≫ g₁) ⁻¹'
      (⋃ E ∈ S.support, AlgebraicGeometry.PrimeDivisor.support E)), y ∈ (c.W : Set Y₂) := by
    intro y
    obtain ⟨p, hpy, hp⟩ := nonempty_inter_closedPoints (Z := closure {g₂ y})
      ⟨g₂ y, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    obtain ⟨c₁, hpc₁⟩ := exists_weakChart_of_isSNC (n := n) (g₁ ≫ π) Ssum hsncS p hp
    obtain ⟨c₂, hc₂⟩ := exists_weakChart_comp_of_etale (g₁ ≫ π) g₂
      (f' := (g₂ ≫ g₁) ≫ π) (Category.assoc _ _ _).symm c₁
    refine ⟨c₂.ofEq (by rw [hZ₁, Set.preimage_preimage]; rfl), ?_⟩
    change y ∈ ((c₂.W : Y₂.Opens) : Set Y₂)
    rw [hc₂]
    exact (specializes_iff_mem_closure.2 hpy).mem_open c₁.W.1.isOpen hpc₁
  -- the reduced inverse image of `S`
  have hdim : topologicalKrullDim Y₂ = topologicalKrullDim V :=
    topologicalKrullDim_eq_of_isFinite_of_isDominant (g₂ ≫ g₁)
  have hfin : topologicalKrullDim V ≠ ⊤ := by
    rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension π n]
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl]
    exact fun h => ENat.natCast_ne_top n (WithBot.coe_injective h)
  obtain ⟨S', hS'snc, hS'E⟩ :=
    exists_isRelativeSNC_reducedPreimage π (g₂ ≫ g₁) hdim hfin S.support hchart
  -- the root
  have hψ₁ := MMP.Fourfold.rationalFunctionsEquivFunctionField_pullbackRationalFunction g₁ ψ hψgen
  refine ⟨Y₂, g₂ ≫ g₁, inferInstance, inferInstance, inferInstance, hrel,
    ((AlgebraicGeometry.isProjectiveVariety_iff_isProjective' ℂ _).1 hproj).2, inferInstance,
    inferInstance, inferInstance, S', hS'snc, hS'E, z, ?_⟩
  rw [hz, hψ₁, functionFieldMap_comp]
  rfl

end MMP.FourfoldProofs.FractionalLogComplexProof
