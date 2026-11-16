module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.Cartier
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleComposition.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleLocal.AffineBasis
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Strict
public import StacksFrontier.AlgebraicGeometry.AmplePullback.QuasiAffineUnitIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleRestrict

/-!
# Twisting a relatively ample sheaf by a pull-back

Let `f : X ⟶ Y` be a morphism of schemes. If `L` is an `f`-ample invertible sheaf on `X` and `M`
is an invertible sheaf on `Y`, then `L ⊗ f^*M` is `f`-ample: over an affine open `V` of `Y` on
which `L` is ample and `M` is trivial, `L ⊗ f^*M` restricts to a sheaf isomorphic to the
restriction of `L`. If `f` is quasi-compact, every ample invertible sheaf on `X` is `f`-ample,
since ampleness restricts to the quasi-compact opens `f⁻¹(V)`.

## Main results

* `MMP.Threefold.Resolution.isRelativelyAmple_tensorModules_modulePullback`: `L ⊗ f^*M` is
  `f`-ample when `L` is.
* `MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple`: an ample invertible sheaf is
  `f`-ample for quasi-compact `f`.
* `MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback`,
  `MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple_divisorialSheaf`: the same two
  statements for Cartier divisors on a normal scheme, `L + f^*B` and `L`.

## Implementation notes

`f`-ampleness is `MMP.Mori.IsRelativelyAmple`, the local form (some affine neighbourhood of each
point of the base). In that form the twist by a pull-back needs no hypothesis on `f`: the
restriction of `L` to `f⁻¹(V)` is ample, so `f⁻¹(V)` is quasi-compact, and so is the preimage of
a basic open of `V` on which `M` is trivial. The passage from ample to `f`-ample needs `f⁻¹(V)`
quasi-compact for affine `V`, which is quasi-compactness of `f`; a projective morphism is proper,
hence quasi-compact. The source states both for a projective morphism of Noetherian schemes.

The tensor product is `Stacks.RelativeVeryAmple.tensorModules` and the pull-back is
`RingedSpaceModuleAdjunction.modulePullback` along `f`, the spellings at which invertibility of a
tensor product and of a pull-back are instances.

For a Cartier divisor `B` on a normal scheme `Y` the pull-back `f^*B` is
`MMP.Mori.Divisor.IsPullback`, defined when `f` maps the generic point of every component of `X`
off `Supp B`; the statement takes the Cartier property of `f^*B` as a hypothesis.

## References

* [J. Kollár, *Lectures on resolution of singularities*][Kollar2007], Lemma 2.9
* [R. Hartshorne, *Algebraic geometry*][Hartshorne1977], II.7
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction MMP.Mori Stacks.Ample

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Threefold.Resolution

/-! ### Relative ampleness of invertible sheaves -/

section Sheaves

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If `V` is an affine open of `Y` with quasi-compact preimage `f⁻¹(V)`, then the preimage of
every quasi-compact open `V' ⊆ V` is quasi-compact: the restriction `f⁻¹(V) ⟶ V` of `f` has
quasi-compact source and affine target, so it is quasi-compact. -/
private theorem compactSpace_preimage_of_le_of_isAffineOpen {V V' : Y.Opens} (hV : IsAffineOpen V)
    [CompactSpace (f ⁻¹ᵁ V).toScheme] (hV' : IsCompact (V' : Set Y)) (h : V' ≤ V) :
    CompactSpace (f ⁻¹ᵁ V').toScheme := by
  haveI : IsAffine V.toScheme := hV
  haveI : QuasiCompact (f ∣_ V) := by
    have : QuasiCompact ((f ∣_ V) ≫ Limits.terminal.from V.toScheme) := by
      rw [Subsingleton.elim ((f ∣_ V) ≫ Limits.terminal.from V.toScheme)
        (Limits.terminal.from _), ← compactSpace_iff_quasiCompact]
      infer_instance
    exact QuasiCompact.of_comp _ (Limits.terminal.from V.toScheme)
  have hW : IsCompact ((V.ι ⁻¹ᵁ V' : V.toScheme.Opens) : Set V.toScheme) :=
    (V.ι.isOpenEmbedding.isInducing.isCompact_preimage_iff (by rwa [Scheme.Opens.range_ι])).mpr hV'
  have h2 := ((f ∣_ V).isCompact_preimage hW).image (f ⁻¹ᵁ V).ι.continuous
  have key (x' : (f ⁻¹ᵁ V).toScheme) : V.ι ((f ∣_ V) x') = f ((f ⁻¹ᵁ V).ι x') :=
    congrArg (fun g => g x') (morphismRestrict_ι f V)
  have heq : ((f ⁻¹ᵁ V).ι '' ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ V') : Set (f ⁻¹ᵁ V).toScheme)) =
      ((f ⁻¹ᵁ V' : X.Opens) : Set X) := by
    ext x
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨x', hx', rfl⟩
      exact (congrArg (· ∈ V') (key x')).mp hx'
    · have hxV : x ∈ f ⁻¹ᵁ V := h hx
      exact ⟨⟨x, hxV⟩, (congrArg (· ∈ V') (key ⟨x, hxV⟩)).mpr hx, rfl⟩
  rw [heq] at h2
  rwa [isCompact_iff_compactSpace] at h2

/-- A trivialization of `M` over an open `V'`, given in the spelling
`AlgebraicGeometry.Scheme.Modules.pullback`, read in the ringed-space spelling `modulePullback`. -/
private def modulePullbackOpensIsoUnit (M : Y.Modules) (V' : Y.Opens)
    (e : (Scheme.Modules.pullback V'.ι).obj M ≅ SheafOfModules.unit V'.toScheme.ringCatSheaf) :
    (modulePullback V'.ι.toLRSHom.toShHom).obj M ≅ Stacks.Ample.unitModule V' :=
  (Adjunction.leftAdjointUniq
      (modulePullbackPushforwardAdjunction V'.ι.toLRSHom.toShHom)
      (Scheme.Modules.pullbackPushforwardAdjunction V'.ι)).app M ≪≫ e

/-- If `M` is trivial over `V'`, then `f^*M` is trivial over `f⁻¹(V')`. -/
private def modulePullbackPreimageIsoUnit (M : Y.Modules) (V' : Y.Opens)
    (e' : (modulePullback V'.ι.toLRSHom.toShHom).obj M ≅ Stacks.Ample.unitModule V') :
    (modulePullback (f ⁻¹ᵁ V').ι.toLRSHom.toShHom).obj
      ((modulePullback f.toLRSHom.toShHom).obj M) ≅ Stacks.Ample.unitModule (f ⁻¹ᵁ V') :=
  (((Stacks.PullbackPseudofunctor.modulePullbackCompIso f.toLRSHom.toShHom
        (f ⁻¹ᵁ V').ι.toLRSHom.toShHom).app M).symm :
      (modulePullback (f ⁻¹ᵁ V').ι.toLRSHom.toShHom).obj
          ((modulePullback f.toLRSHom.toShHom).obj M) ≅
        (modulePullback ((f ⁻¹ᵁ V').ι ≫ f).toLRSHom.toShHom).obj M) ≪≫
    (eqToIso (by rw [morphismRestrict_ι]) :
      (modulePullback ((f ⁻¹ᵁ V').ι ≫ f).toLRSHom.toShHom).obj M ≅
        (modulePullback ((f ∣_ V') ≫ V'.ι).toLRSHom.toShHom).obj M) ≪≫
    ((Stacks.PullbackPseudofunctor.modulePullbackCompIso V'.ι.toLRSHom.toShHom
        (f ∣_ V').toLRSHom.toShHom).app M :
      (modulePullback ((f ∣_ V') ≫ V'.ι).toLRSHom.toShHom).obj M ≅
        (modulePullback (f ∣_ V').toLRSHom.toShHom).obj
          ((modulePullback V'.ι.toLRSHom.toShHom).obj M)) ≪≫
    Stacks.AmplePullback.modulePullbackIsoUnitModule (f ∣_ V') _ e'

/-- If `M` is trivial over `V'`, then the restrictions of `L ⊗ f^*M` and of `L` to `f⁻¹(V')`
are isomorphic. -/
private def pullbackTensorModulePullbackIso (L : X.Modules) (M : Y.Modules) (V' : Y.Opens)
    (e' : (modulePullback V'.ι.toLRSHom.toShHom).obj M ≅ Stacks.Ample.unitModule V') :
    Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V').ι
      (Stacks.RelativeVeryAmple.tensorModules X L ((modulePullback f.toLRSHom.toShHom).obj M)) ≅
      Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V').ι L :=
  Stacks.RelativeVeryAmple.pullbackTensorModulesIso (f ⁻¹ᵁ V').ι L _ ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso (f ⁻¹ᵁ V') (Iso.refl _)
      (modulePullbackPreimageIsoUnit f M V' e') ≪≫
    Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor (f ⁻¹ᵁ V') _

/-- **A pull-back twist does not change relative ampleness.** If `L` is an `f`-ample invertible
sheaf on `X` and `M` an invertible sheaf on `Y`, then `L ⊗ f^*M` is `f`-ample. -/
@[mmp "lem_mmp_foundation_relative_ample_pullback_twist"]
theorem isRelativelyAmple_tensorModules_modulePullback (L : X.Modules) [IsInvertibleModule X L]
    (M : Y.Modules) [IsInvertibleModule Y M] (hL : IsRelativelyAmple f L) :
    haveI := Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules X L
      ((modulePullback f.toLRSHom.toShHom).obj M)
    IsRelativelyAmple f
      (Stacks.RelativeVeryAmple.tensorModules X L ((modulePullback f.toLRSHom.toShHom).obj M)) := by
  haveI := Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules X L
    ((modulePullback f.toLRSHom.toShHom).obj M)
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := hL y
  obtain ⟨V', hV', hyV', hV'V, ⟨e⟩⟩ :=
    @Stacks.Modules.exists_affineOpen_pullback_iso_unit_of_isInvertible _ M ‹_› _ _ hyV
  refine ⟨V', hV', hyV', ?_⟩
  haveI : CompactSpace (f ⁻¹ᵁ V).toScheme := hamp.1
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (pullbackTensorModulePullbackIso f L M V' (modulePullbackOpensIsoUnit M V' e))).mpr
    (Stacks.RelativeAmpleComposition.isAmple_restrict_of_le (f.preimage_mono hV'V) L hamp
      (compactSpace_preimage_of_le_of_isAffineOpen f hV hV'.isCompact hV'V))

/-- **An ample invertible sheaf is relatively ample.** If `f` is quasi-compact (for instance
projective), every ample invertible sheaf on `X` is `f`-ample. -/
@[mmp "lem_mmp_foundation_relative_ample_pullback_twist"]
theorem isRelativelyAmple_of_isAmple [QuasiCompact f] (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) : IsRelativelyAmple f L := by
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  haveI := Stacks.RelativeAmpleComposition.compactSpace_preimage_of_isCompact f V hV.isCompact
  exact ⟨V, hV, hyV, Stacks.AmpleRestrict.isAmple_pullbackModule_ι (f ⁻¹ᵁ V) L hL⟩

end Sheaves

/-! ### Relative ampleness of Cartier divisors -/

section Divisors

variable {X Y : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Y)

/-- The restriction of a module to an open subscheme, in the ringed-space spelling `modulePullback`
of the pull-back, is the restriction `AlgebraicGeometry.Scheme.Modules.restrict`. -/
private def modulePullbackIsoRestrict {Z : Scheme.{u}} (U : Z.Opens) (F : Z.Modules) :
    (modulePullback U.ι.toLRSHom.toShHom).obj F ≅ F.restrict U.ι :=
  (Adjunction.leftAdjointUniq
      (modulePullbackPushforwardAdjunction U.ι.toLRSHom.toShHom)
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι)).app F ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm

/-- If `L` is an `f`-ample Cartier divisor on `X` and `B` a Cartier divisor on the normal scheme
`Y` with pull-back `f^*B`, then `L + f^*B` is `f`-ample. -/
theorem isRelativelyAmple_add_of_isPullback [IsLocallyNoetherian Y] [IsNormal Y]
    {L : Divisor X} (hL : L.IsCartier) (hLf : L.IsRelativelyAmple f hL) {B : Divisor Y}
    (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (hB' : B.IsPullback f hB B') (hB'c : B'.IsCartier) :
    (L + B').IsRelativelyAmple f (hL.add hB'c) := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := (hL.add hB'c).isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := hLf y
  obtain ⟨U, hyU, φ, hφ⟩ := hBc y
  obtain ⟨V', hV', hyV', hV'le⟩ :=
    exists_isAffineOpen_mem_and_subset (U := V ⊓ U) (show y ∈ V ⊓ U from ⟨hyV, hyU⟩)
  have hV'V : V' ≤ V := fun z hz => (hV'le hz).1
  have hV'U : V' ≤ U := fun z hz => (hV'le hz).2
  refine ⟨V', hV', hyV', ?_⟩
  haveI : CompactSpace (f ⁻¹ᵁ V).toScheme := hamp.1
  have hc : CompactSpace (f ⁻¹ᵁ V').toScheme :=
    compactSpace_preimage_of_le_of_isAffineOpen f hV hV'.isCompact hV'V
  have hLV' : IsAmple (f ⁻¹ᵁ V').toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V').ι L.divisorialSheaf) :=
    Stacks.RelativeAmpleComposition.isAmple_restrict_of_le (f.preimage_mono hV'V)
      L.divisorialSheaf hamp hc
  -- the pull-back of the local equation `φ` of `B`, a local equation of `B'` on `f⁻¹(U)`
  classical
  let ψ : (RationalFunctions X)ˣ := (RationalFunctions.unitsEquiv X).symm fun Z =>
    if hZ : f (componentGenericPoint X Z) ∈ U then pullbackComponent f hB hφ Z hZ else 1
  have hψ : ∀ E : Mori.PrimeDivisor X, (E.support ∩ ((f ⁻¹ᵁ U : X.Opens) : Set X)).Nonempty →
      B'.coeff E = E.ord ψ := by
    intro E hE
    rw [hB' U φ hφ E hE]
    change _ = E.ordUnit (if hZ : f (componentGenericPoint X E.component) ∈ U then
      pullbackComponent f hB hφ E.component hZ else 1)
    rw [dif_pos (E.map_componentGenericPoint_mem f hE)]
  have e : (L + B').divisorialSheaf.restrict (f ⁻¹ᵁ V').ι ≅
      L.divisorialSheaf.restrict (f ⁻¹ᵁ V').ι :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V').ι).mapIso
        (Divisor.divisorialSheafMulIso ψ (D' := L + B' - principalDivisor ψ) fun E => by
          rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, sub_add_cancel]) ≪≫
      Divisor.restrictDivisorialSheafIsoOfEqOn fun E hE => by
        rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
          hψ E (hE.mono (Set.inter_subset_inter_right _ (f.preimage_mono hV'U))),
          add_sub_cancel_right]
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (modulePullbackIsoRestrict _ _ ≪≫ e ≪≫ (modulePullbackIsoRestrict _ _).symm)).mpr hLV'

/-- If `f` is quasi-compact, an ample Cartier divisor on `X` is `f`-ample. -/
theorem isRelativelyAmple_of_isAmple_divisorialSheaf [QuasiCompact f] {L : Divisor X}
    (hL : L.IsCartier)
    (hamp : haveI := hL.isInvertibleModule_divisorialSheaf; IsAmple X L.divisorialSheaf) :
    L.IsRelativelyAmple f hL :=
  haveI := hL.isInvertibleModule_divisorialSheaf
  isRelativelyAmple_of_isAmple f L.divisorialSheaf hamp

end Divisors

/-! ### Closed subsets of quasi-projective varieties -/

end MMP.Threefold.Resolution
