module
public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.CohomologySurjective
public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.Iterated
public import MMP.AlgebraicGeometry.Singularities.SmoothZeroSchemeSNC
public import MMP.Algebra.Category.ModuleCat.Sheaf.RelLocallyExactQuasiIso

/-!
# Surjectivity of multiplication by a power of a section with smooth zero scheme

Let `X` be a smooth projective variety over `ℂ`, `L` an invertible `𝒪_X`-module, `m ≥ 2`, and
`s` a nonzero global section of `L^{⊗m}` whose zero scheme `D` is smooth over `ℂ`. For
`0 < r < m` and `k ≥ 0`, multiplication by `s^k` is a morphism
`L^{⊗ -(r + mk)} ⟶ L^{⊗ -r}`, and it induces a surjection
`H^i(X, L^{⊗ -(r + mk)}) ⟶ H^i(X, L^{⊗ -r})` in every degree `i`. Applied with `r = 1` and
`L^{⊗m}` very ample, this reduces Kodaira vanishing to Serre vanishing.

## Main results

* `MMP.Mori.surjective_derivedCohomologyOverField_map_chain_of_smooth_zeroScheme`: the
  surjectivity of the map induced on cohomology by multiplication by `s^k`.

## Implementation notes

* `L^{⊗n}` for `n : ℤ` is `Stacks.Ample.tensorPowModule X L n`, Stacks Tag 01CU.
* Multiplication by `s^k` is the `k`-fold composite of multiplication by `s`,
  `Stacks.EnriquesSeveriZariski.chain L s 𝒪_X (-r) k`, a morphism
  `𝒪_X ⊗ L^{⊗ (-r - k m)} ⟶ 𝒪_X ⊗ L^{⊗ -r}` (the source degree is
  `Stacks.EnriquesSeveriZariski.descend m (-r) k = -r - k m`). The factor `𝒪_X ⊗ -` is the
  twist of `𝒪_X` by the powers of `L`; it is canonically isomorphic to the powers themselves,
  which does not change surjectivity on cohomology.
* `H^i(X, ℱ)` for `i : ℤ` is `Stacks.Duality.derivedCohomologyOverField f` of `ℱ` placed in
  degree zero, as in
  `MMP.Mori.subsingleton_derivedCohomologyOverField_dualSheaf_of_isAmple_complex`; the map on
  cohomology is the image of the morphism of sheaves under the functors defining it.
* The zero scheme is `AlgebraicGeometry.zeroScheme`, and its smoothness is smoothness over `ℂ`
  of the composite of its closed immersion with the structure morphism.

## References

* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  proof of Theorem 2.47
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Stacks.SmallDerivedModel

namespace MMP.Mori

/-- **Multiplication by a power of a section with smooth zero scheme is surjective on
cohomology.** Let `X` be a smooth projective variety over `ℂ`, `L` an invertible `𝒪_X`-module,
`m ≥ 2`, and `s` a nonzero global section of `L^{⊗m}` with smooth zero scheme. For `0 < r < m`
and `k ≥ 0`, multiplication by `s^k` induces a surjection
`H^i(X, L^{⊗ -(r + mk)}) ⟶ H^i(X, L^{⊗ -r})`. -/
@[mmp "lem_mmp_lc_bpf_kodaira_twist_surjective"]
public theorem surjective_derivedCohomologyOverField_map_chain_of_smooth_zeroScheme
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ f] (hsm : IsSmoothScheme f)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {m : ℕ} (hm : 2 ≤ m)
    (s : Γ(Stacks.Ample.tensorPowModule X L (m : ℤ), ⊤)) (hs : s ≠ 0)
    (hD : Smooth ((@AlgebraicGeometry.zeroScheme X (Stacks.Ample.tensorPowModule X L (m : ℤ))
      (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subschemeι ≫ f))
    {r : ℕ} (hr0 : 0 < r) (hrm : r < m) (k : ℕ) (i : ℤ) :
    Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) i).map
      ((derivedGlobalSectionsOver f).map
        ((DerivedCategory.singleFunctor X.Modules 0).map
          (Stacks.EnriquesSeveriZariski.chain L s (Stacks.Ample.unitModule X) (-r) k)))).hom := by
  open MMP.LcBpf MMP.FourfoldProofs.FractionalLogComplexProof in
  (
      rcases lt_or_ge i 0 with hi | hi
      · exact surjective_homology_map_of_neg f _ hi
      obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = (q : ℤ) := ⟨i.toNat, by omega⟩
      obtain ⟨hlN, hnorm⟩ :=
        MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm
      haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      have hcart : ∀ D : Divisor X, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
      have hπ : IsProjective f :=
        IsProjectiveMorphism.isProjective (IsProjectiveVariety.isProjective (f := f))
      have hsmooth : Smooth f := (MMP.Mori.isSmoothScheme_iff f).1 hsm
      obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim X = d := by
        have h := Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ f (genericPoint X)
        rw [(genericPoint_spec X).def, ← IsHomeomorph.topologicalKrullDim_eq _
          (Homeomorph.Set.univ X).isHomeomorph] at *
        exact ⟨_, h⟩
      haveI : SmoothOfRelativeDimension d f :=
        MMP.Intersection.smoothOfRelativeDimension_of_isVariety f d hd
      obtain ⟨M₁, ⟨eM⟩⟩ := exists_divisorialSheaf_iso_of_isInvertible L
      obtain ⟨D, hDs⟩ := exists_isSectionDivisor L s hs
      obtain ⟨ψ, hψ⟩ := hDs.exists_eq_add_principalDivisor hcart M₁ eM
      have hDE : ∀ E, D E = 0 ∨ D E = 1 := coeff_eq_zero_or_one_of_smooth_zeroScheme f L s hD D hDs
      have hD0 : ∀ E, 0 ≤ D E := fun E => by rcases hDE E with h | h <;> omega
      have hSNC : D.IsRelativeSNC d f := isRelativeSNC_of_smooth_zeroScheme f hsm L s hs hD D hDs d
      have hpow : ∀ n : ℕ, principalDivisor (ψ ^ n) = (n : ℤ) • principalDivisor ψ := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, MMP.Mori.principalDivisor_mul, ih]
          push_cast
          rw [add_smul, one_smul]
      set M : Divisor X := (r : ℤ) • M₁ with hMdef
      set Bn : Divisor X := (r : ℤ) • D with hBndef
      have hBnE : ∀ E, Bn E = r * D E := fun E => by
        simp only [hBndef, Finsupp.smul_apply, smul_eq_mul]
      have hSB : ∀ E, D E = (0 : Divisor X) E + if Bn E = 0 then 0 else 1 := by
        intro E
        rw [hBnE]
        rcases hDE E with h | h <;> rw [h] <;> simp <;> omega
      have hB : ∀ E, 0 ≤ Bn E ∧ Bn E < m := by
        intro E
        rw [hBnE]
        rcases hDE E with h | h <;> rw [h] <;> constructor <;> push_cast <;> omega
      have hψr : (m : ℤ) • M = Bn + principalDivisor (ψ ^ r) := by
        have hψ' : (m : ℤ) • M₁ = D + principalDivisor ψ := by rwa [natCast_zsmul]
        rw [hpow, hMdef, hBndef, smul_smul, mul_comm, ← smul_smul, hψ', smul_add]
      have hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support := fun E hE =>
        Finsupp.mem_support_iff.2 fun h => hE (by rw [hBnE, h, mul_zero])
      obtain ⟨u, hu⟩ := exists_section_eq_ratRes D M Bn m (ψ ^ r) hψr hBD
      obtain ⟨K, F, e, ι, hK⟩ := exists_isCModel_of_nonneg d f D hSNC 0 M le_rfl Bn hSB m
        (by omega) (fun E => (hB E).1) (ψ ^ r) hψr u hu
      have hNu : IsUnit ((m : Γ(X, cU' D M)) * u) := by
        have hNW : IsUnit (m : Γ(X, cU' D M)) := by
          let φ : ℂ →+* Γ(X, cU' D M) := (X.presheaf.map (homOfLE le_top).op).hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)
          simpa only [map_natCast] using
            ((Nat.cast_ne_zero.2 (by omega : m ≠ 0)).isUnit : IsUnit (m : ℂ)).map φ
        refine hNW.mul (isUnit_of_ord_eq_zero u (ψ ^ r) hu fun E hE => ?_)
        obtain ⟨y, hyE, hyU⟩ := hE
        have hME : M E = 0 := by
          by_contra h
          exact hyU (Or.inr (MMP.Mori.DivisorWithCoeffs.support_subset_supp h hyE))
        have hB0 : Bn E = 0 := by
          by_contra h
          exact hyU (Or.inl (MMP.Mori.DivisorWithCoeffs.support_subset_supp
            (Finsupp.mem_support_iff.1 (hBD E h)) hyE))
        have h := congrArg (fun F => F E) hψr
        simp only [Finsupp.smul_apply, Finsupp.add_apply, hME, hB0, smul_zero, zero_add] at h
        rw [← MMP.Mori.coeff_principalDivisor]
        exact h.symm
      obtain ⟨M', hMk, hM, K', F', e', ι', hK', φ, hφ, hmono, hrel⟩ :=
        reach_nsmul Bn hSB (by omega) (fun E => (hB E).1) (ψ ^ r) hψr hu hNu hK k
      haveI : QuasiIso φ := quasiIso_of_relLocallyExact φ hrel
      have hle : -M' ≤ -M := by
        rw [hMk]
        intro E
        have h0 : 0 ≤ (k : ℤ) * D E := mul_nonneg (by positivity) (hD0 E)
        simp only [Finsupp.neg_apply, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
        omega
      have hedge := surjective_homology_map_divisorialSheafInclusion_of_isTwistInclusion d f hπ D
        hSNC Bn hSB m (by omega) hB M (ψ ^ r) hψr u hu hK hK' hM hle φ hφ q
      have h : -((r : ℤ) • M₁) - (k : ℤ) • D ≤ -((r : ℤ) • M₁) := by
        intro E
        have h0 : 0 ≤ (k : ℤ) * D E := mul_nonneg (by positivity) (hD0 E)
        simp only [Finsupp.neg_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
        omega
      exact (surjective_homology_map_chain_iff_divisorialSheafInclusion f hcart L M₁ eM s hDs r k h
        q).2 <| (surjective_map_divisorialSheafInclusion_congr
        (DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (q : ℤ))
        (by rw [hMk, hMdef, neg_add']; congr 1) hle h).1 hedge)

end MMP.Mori
