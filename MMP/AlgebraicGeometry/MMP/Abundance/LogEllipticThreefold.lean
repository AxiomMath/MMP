module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.FibrationExtension
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.EquidimensionalExtension
public import MMP.AlgebraicGeometry.MMP.Abundance.NumericalDimensionOnePencil
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.EquidimensionalPullback
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.DescendedBundleAmple
public import MMP.AlgebraicGeometry.MMP.Abundance.NoTriviallyConnectedReduction
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Curves.Maps.CoefficientSpace
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold

/-!
# Abundance for log elliptic threefolds

Let `X` be a projective `ℚ`-factorial threefold and `Δ_X` a boundary `ℚ`-divisor with
`(X, Δ_X)` klt, such that `K_X + Δ_X` is nef, some Cartier multiple `m(K_X + Δ_X)` moves in a
linear system of dimension at least one, and some nonempty open `U ⊆ X` carries a log elliptic
fiber space `f_U : (U, Δ_X|_U) ⟶ Z`; that is, `(X, Δ_X)` satisfies the assumptions of FA 15.4
(`MMP.Flips.SatisfiesAbundanceAssumptions`). Then `K_X + Δ_X` is eventually free: some positive
multiple of it is a base point free Cartier divisor (`MMP.Flips.IsEventuallyFree`).

## Main results

* `MMP.Flips.SatisfiesAbundanceAssumptions.isEventuallyFree`: FA Thm. 15.4.

## Implementation notes

The statement is over `ℂ`, the ground field of FA Chapter 15.
The canonical divisor `K_X` is an integral Weil divisor recorded in
`MMP.Flips.SatisfiesAbundanceAssumptions` (klt includes that `K_X` is canonical).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Thm. 15.4
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Flips MMP.Mori

namespace Proof_thm_fa15_log_elliptic_abundance

universe u

open Stacks.Ample Stacks.RelativeVeryAmple in
/-- On the nonvanishing locus of a nonzero section `σ` of `𝒪_X(M)`, `M` Cartier, the divisor of
zeros `(σ)₀` vanishes: multiplication by `σ⁻¹` identifies `𝒪_X(M)` with `𝒪_X((σ)₀)`, sending `σ`
to the canonical section `1`, whose nonvanishing locus is the complement of `Supp (σ)₀`. -/
private theorem notMem_supp_zeroDivisor_of_mem_nonvanishingLocus {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {M : Divisor X} (hM : M.IsCartier)
    (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) {x : X}
    (hx : x ∈ nonvanishingLocus M.divisorialSheaf σ) : x ∉ (M.zeroDivisor σ hσ).supp := by
  have hZ : 0 ≤ M.zeroDivisor σ hσ := M.zeroDivisor_nonneg σ hσ
  have hZc : (M.zeroDivisor σ hσ).IsCartier := by
    rw [Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hM
  have hcoeff : ∀ E : MMP.Mori.PrimeDivisor X, M.coeff E =
      (M.zeroDivisor σ hσ).coeff E + E.ord (Divisor.isUnit_sectionToRationalFunctions hσ).unit⁻¹ := by
    intro E
    rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
      PrimeDivisor.ord_inv]
    ring
  let e := Divisor.divisorialSheafMulIso _ hcoeff
  have he : e.hom.app ⊤ σ = MMP.Threefold.Mori.oneSection hZ := by
    refine Subtype.ext (funext fun Z => ?_)
    change ((Divisor.isUnit_sectionToRationalFunctions hσ).unit⁻¹ : (RationalFunctions X)ˣ).1 Z.1 *
        σ.1 Z = ((Divisor.structureSheafToDivisorialSheaf hZ).app ⊤ (1 : Γ(X, ⊤))).1 Z
    rw [Divisor.coe_structureSheafToDivisorialSheaf_app, map_one]
    have h1 : σ.1 Z = ((Divisor.isUnit_sectionToRationalFunctions hσ).unit :
        RationalFunctions X) Z.1 := rfl
    rw [h1, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rfl
  rw [← Stacks.CokernelSupport.nonvanishingLocus_iso_app e σ, he,
    MMP.Threefold.Mori.nonvanishingLocus_oneSection hZ hZc] at hx
  exact hx

/-- A Cartier divisor `M` such that every point lies in the nonvanishing locus of some global
section of `𝒪_X(M)` is base point free. -/
private theorem isBasepointFree_of_forall_mem_nonvanishingLocus {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {M : Divisor X} (hM : M.IsCartier)
    (h : ∀ x : X, ∃ σ : Γ(M.divisorialSheaf, ⊤),
      x ∈ Stacks.Ample.nonvanishingLocus M.divisorialSheaf σ) :
    M.IsBasepointFree := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨σ, hσx⟩ := h x
  have hσ : (σ : M.divisorialSubmodule ⊤) ≠ 0 := by
    rintro (h0 : σ = 0)
    rw [h0, Stacks.Ample.nonvanishingLocus_zero] at hσx
    exact hσx
  exact notMem_supp_zeroDivisor_of_mem_nonvanishingLocus hM σ hσ hσx
    ((Divisor.mem_baseLocus_iff M x).mp hx σ hσ)

/-- Eventually free and composed of a pencil implies eventually free. -/
private theorem isEventuallyFree_of_isEventuallyFreePencil
    {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {L : QDivisor X}
    (h : IsEventuallyFreePencil k sX L) : IsEventuallyFree k sX L := by
  obtain ⟨m, hm, M, hML, hX, hMc, ι, b, hloc, -⟩ := h
  refine ⟨⟨hX.toIsVariety, inferInstance⟩, m, hm, M, hML, hMc, ?_⟩
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  haveI := hMc.isInvertibleModule_divisorialSheaf
  refine isBasepointFree_of_forall_mem_nonvanishingLocus hMc fun x => ?_
  have hx : x ∈ linearSystemLocus k M.divisorialSheaf b := by rw [hloc]; trivial
  obtain ⟨i, hi⟩ := (mem_linearSystemLocus_iff k M.divisorialSheaf b x).mp hx
  exact ⟨b i, hi⟩

open Stacks.Ample Stacks.RelativeVeryAmple in
/-- If `𝒪_X(N) ≅ f^* 𝓛` for a Cartier divisor `N`, then `𝒪_X(nN) ≅ f^* 𝓛^{⊗ n}` for `n ≥ 1`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso_pullback_tensorPowModule {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Y) {N : Divisor X}
    (hN : N.IsCartier) (L : Y.Modules) [IsInvertibleModule Y L]
    (e : N.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj L) (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((n • N).divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (tensorPowModule Y L (n : ℤ))) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [one_nsmul]
    exact ⟨e ≪≫ (Scheme.Modules.pullback f).mapIso (tensorPowModuleOneIso Y L).symm⟩
  | succ n hn ih =>
    obtain ⟨ie⟩ := ih
    rw [succ_nsmul]
    exact ⟨((hN.nsmul n).divisorialSheafTensorIso hN).symm ≪≫ tensorModulesMapIso X ie e ≪≫
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso f _ _).symm ≪≫
      (Scheme.Modules.pullback f).mapIso
        (tensorModulesMapIso Y (Iso.refl _) (tensorPowModuleOneIso Y L).symm ≪≫
          tensorPowModuleAddIso Y L (n : ℤ) 1 ≪≫
          tensorPowModuleCongr Y L (by push_cast; ring))⟩

/-- `ν ≤ 1` gives a free pencil (`lem_fa15_nu_one_free_pencil`). -/
private theorem isEventuallyFreePencil_of_numericalDimension_le_one
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X]
    [CompactSpace X] [LocallyOfFiniteType sX] [QuasiCompact sX]
    {K : Divisor X} {Δ : QDivisor X} (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (hν : haveI := h.isProjectiveVariety
      numericalDimension k sX inferInstance (Divisor.toQDivisor K + Δ) h.isNef ≤ 1) :
    IsEventuallyFreePencil k sX (Divisor.toQDivisor K + Δ) :=
  h.isEventuallyFreePencil_of_numericalDimension_le_one hν

/-- The case `ν ≥ 2` without trivially connected prime divisors (FA 15.10–15.13). -/
private theorem isEventuallyFree_of_two_le_numericalDimension
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (hD : ∀ D : MMP.Mori.PrimeDivisor X, ¬ IsTriviallyConnected k sX 3 K Δ (Finsupp.single D 1))
    (hν : haveI := h.isProjectiveVariety
      2 ≤ numericalDimension k sX inferInstance (Divisor.toQDivisor K + Δ) h.isNef) :
    IsEventuallyFree k sX (Divisor.toQDivisor K + Δ) := by
  obtain ⟨U, hU, Z, sZ, fU, hfU⟩ := h.exists_isLogEllipticFiberSpace
  obtain ⟨Zbar, sZbar, Z₀, j, f, hZbar, hZbarP, hdim, hZ₀, hj, hjs, hf, hconn, hfib, hfj⟩ :=
    exists_extension_of_forall_not_isTriviallyConnected sX h U hU sZ fU hfU hD
  have hlog : IsLogEllipticFiberSpace k sX sZbar 3 K Δ f :=
    isLogEllipticFiberSpace_of_forall_not_isTriviallyConnected sX h U hU sZ fU hfU hD sZbar Z₀ j
      f hZbar hZbarP hdim hZ₀ hjs hf hconn hfib hfj
  have hlc : IsLogCanonical sX 3 K (QDivisor.toRDivisor Δ) := by
    obtain ⟨h1, h2, h3, h4⟩ := h.isKawamataLogTerminal
    exact (isLogCanonical_iff_logDiscrepancy sX 3 K _).mpr
      ⟨h1, h2, h3, fun F hF b hb => (h4 F hF b hb).le⟩
  obtain ⟨n, hn, N, hN, 𝓛, h𝓛, ⟨e⟩⟩ := hlog.exists_divisorialSheaf_iso_pullback hfib hlc h.isNef
  haveI := h𝓛
  have hamp := isAmple_of_divisorialSheaf_iso_pullback sX h hD hν U hU sZ fU hfU sZbar Z₀ j f
    hZbar hZbarP hdim hZ₀ hjs hf hconn hfib hfj 𝓛 hn N hN e
  have hNc : N.IsCartier := fun x => by
    obtain ⟨V, hxV, ψ, hψ⟩ :=
      MMP.Fourfold.exists_isLocalEquation_preimage_of_iso_pullback f 𝓛 e (f x)
    exact ⟨f ⁻¹ᵁ V, hxV, ψ, hψ⟩
  obtain ⟨N₀, r, s, hN₀, hgen, -⟩ :=
    Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple _ hamp
  obtain ⟨e'⟩ := nonempty_divisorialSheaf_nsmul_iso_pullback_tensorPowModule f hNc 𝓛 e N₀ hN₀
  refine ⟨h.isQFactorial.1, N₀ * n, Nat.mul_pos (by omega) hn, N₀ • N, ?_, hNc.nsmul N₀, ?_⟩
  · rw [map_nsmul, hN, ← natCast_zsmul, smul_smul]
    push_cast
    rfl
  · refine isBasepointFree_of_forall_mem_nonvanishingLocus (hNc.nsmul N₀) fun x => ?_
    obtain ⟨i, hi⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks s hgen
      (f x)
    refine ⟨e'.inv.app ⊤ (AlgebraicGeometry.pullbackGlobalSections f _ (s i)), ?_⟩
    rw [← Iso.symm_hom, Stacks.CokernelSupport.nonvanishingLocus_iso_app e'.symm]
    exact (MMP.Fourfold.mem_nonvanishingLocus_pullbackGlobalSections_iff f _ (s i) x).mpr hi

private theorem solution
    {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions ℂ sX K Δ) :
    IsEventuallyFree ℂ sX (Divisor.toQDivisor K + Δ) := by
  rcases h.isEventuallyFreePencil_or_exists_forall_not_isTriviallyConnected with hp | ⟨X', sX', _, _, _, _, _, _, K', Δ', h',
    hD', himp⟩
  · exact isEventuallyFree_of_isEventuallyFreePencil sX hp
  · refine himp ?_
    haveI := h'.isProjectiveVariety
    by_cases hν : numericalDimension ℂ sX' inferInstance (Divisor.toQDivisor K' + Δ') h'.isNef ≤ 1
    · exact isEventuallyFree_of_isEventuallyFreePencil sX'
        (isEventuallyFreePencil_of_numericalDimension_le_one h' hν)
    · exact isEventuallyFree_of_two_le_numericalDimension sX' h' hD' (by omega)

end Proof_thm_fa15_log_elliptic_abundance

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

/-- **Abundance for log elliptic threefolds** (FA Thm. 15.4). Let `X` be a projective
`ℚ`-factorial threefold over `ℂ`, `K_X` a
canonical divisor and `Δ_X` a boundary `ℚ`-divisor such that `(X, Δ_X)` satisfies the assumptions
of 15.4 (`MMP.Flips.SatisfiesAbundanceAssumptions`): `(X, Δ_X)` is klt, `K_X + Δ_X` is nef,
`dim |m(K_X + Δ_X)| ≥ 1` for some `m > 0` with `m(K_X + Δ_X)` Cartier, and a nonempty open
`U ⊆ X` carries a log elliptic fiber space `f_U : (U, Δ_X|_U) ⟶ Z`. Then `K_X + Δ_X` is
eventually free (`MMP.Flips.IsEventuallyFree`). -/
@[mmp "thm_fa15_log_elliptic_abundance"]
public theorem SatisfiesAbundanceAssumptions.isEventuallyFree
    {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions ℂ sX K Δ) :
    IsEventuallyFree ℂ sX (Divisor.toQDivisor K + Δ) :=
      by revert X sX K Δ h; first | exact Proof_thm_fa15_log_elliptic_abundance.solution | exact Proof_thm_fa15_log_elliptic_abundance.solution _ | exact Proof_thm_fa15_log_elliptic_abundance.solution _ _ | exact Proof_thm_fa15_log_elliptic_abundance.solution _ _ _ | exact Proof_thm_fa15_log_elliptic_abundance.solution _ _ _ _

end MMP.Flips

