module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChain
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Singularities.Terminal.ConventionsAgree
import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
import MMP.AlgebraicGeometry.MMP.Contraction.RelativeNegativeRay
import MMP.AlgebraicGeometry.MMP.Threefold.Flip.KltFlipExistence
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.BridgeLabels
import MMP.Analysis.Complex.CauchyOsgoodLaurent
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.TerminalFlips
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionLabels
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# A bridge programme from the decreased boundary reaches a nef end

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized tail of threefolds with common
low-discrepancy set `I_∞`, fix `i`, and let `(p_i, Θ_i)`, `p_i : Y_i ⟶ X_i`, be a crepant junction
of `(X_i, B_i)` extracting `I_∞`, with decreased boundary `Θ_i'`. Then there is a finite relative
threefold programme over `Z_i` (via `f_i ∘ p_i`) from `(Y_i, Θ_i')` in which every contraction
`g_k` is small, every model `(V_k, Θ_k)` is an effective rational terminal pair on a normal
projective `ℚ`-factorial threefold, and whose end `(V_m, Θ_m)` has `K_{V_m} + Θ_m` nef over `Z_i`.
It is the `(K_{Y_i} + Θ_i')`-MMP over `Z_i`: a divisorial contraction would lose a divisor whose
log discrepancy over `(X_{i+1}, B_{i+1})` is at most one, so every step is a flip, and flips of
terminal threefold pairs terminate.

## Main results

* `MMP.Fourfold.StabilizedTail.IsDecreasedBoundary.exists_relativeThreefoldProgram`: the
  programme exists, for any canonical divisor `K` of `Y_i` with which it is run.

## Implementation notes

The programme is run with a canonical divisor `K` of `Y_i`, which the structure
`MMP.Fourfold.RelativeThreefoldProgram` carries; the statement holds for every choice of `K`.
The models of a programme are `V_k` for `k ≤ m`; the data indexed beyond `m` are unconstrained,
so the properties of the models are asserted for `k ≤ m` only. Nefness over `Z_i` is
`MMP.Mori.QDivisor.IsRelativelyNef` along `π_m : V_m ⟶ Z_i`, which includes that
`K_{V_m} + Θ_m` is `ℚ`-Cartier.
-/

section

open CategoryTheory AlgebraicGeometry

namespace Proof_lem_mmp_indexc_bridge_program

open MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedTail

/-! ### General lemmas -/

section General

/-- A klt pair with rational boundary is dlt. -/
private theorem isDltPair_of_isKltPair {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} (hB : MMP.Fourfold.IsKltPair sX B) :
    MMP.Intersection.IsDltPair sX B := by
  obtain ⟨-, n, K, hK, -⟩ := hB.1.isPair
  have hM := (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hK hB.1).mp hB
  exact (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK B).mpr
    (MMP.Threefold.Mori.IsKltPair.isDltPair hM hB.1.nonneg).1

/-- The identity of a normal variety is small. -/
private theorem isSmallMorphism_id {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) : IsSmallMorphism sX sX (𝟙 X) := by
  refine ⟨hX, hX, Category.id_comp _, inferInstance, isBirationalMorphism_of_isIso _, ?_⟩
  rw [le_closedsCodimension_iff]
  intro W hW
  exfalso
  obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
  have hx' := hW hx
  rw [SetLike.mem_coe, mem_exceptionalSet] at hx'
  exact hx' (le_biregularLocus ((isBiregular_top_iff _).mpr inferInstance) trivial)

/-- Every `ℚ`-Cartier `ℚ`-divisor has a multiple which is ample relative to an isomorphism. -/
private theorem hasRelativelyAmpleMultiple_of_isIso {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (e : X ⟶ Y) [IsIso e] {D : QDivisor X}
    (hD : D.IsQCartier) : D.HasRelativelyAmpleMultiple e := by
  obtain ⟨m, hm, L, hL, hLc⟩ := hD.exists_pos
  refine ⟨m, hm, L, hLc, hL, ?_⟩
  haveI := hLc.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  refine ⟨V, hV, hyV, ?_⟩
  haveI : IsAffine (e ⁻¹ᵁ V) := hV.preimage e
  have hinv : Stacks.Ample.IsInvertibleModule (e ⁻¹ᵁ V).toScheme
      ((RingedSpaceModuleAdjunction.modulePullback (e ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        L.divisorialSheaf) := inferInstance
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
    (@AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible _ _ _ _ hinv)

/-- The birational transform of divisors commutes with regarding divisors as `ℚ`-divisors. -/
private theorem transformDivisor_toQDivisor {X Y : Scheme.{0}} (f : RationalMap X Y)
    (D : Divisor X) :
    f.transformDivisor (Divisor.toQDivisor D) = Divisor.toQDivisor (f.transformDivisor D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  | single P n =>
    rw [MMP.Threefold.Resolution.toQDivisor_single, RationalMap.transformDivisor_single,
      RationalMap.transformDivisor_single]
    rcases f.transformPrimeDivisor P with _ | E
    · simp
    · exact (MMP.Threefold.Resolution.toQDivisor_single E n).symm

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with regarding divisors as `ℚ`-divisors. -/
private theorem flipTransform_toQDivisor {X X' Y : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : Divisor X) :
    flipTransform f fp (Divisor.toQDivisor D) = Divisor.toQDivisor (flipTransform f fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, transformDivisor_toQDivisor,
    MMP.Threefold.Resolution.inverseTransformDivisor_toQDivisor]

/-- A projective morphism in the sense of EGA to an H-projective variety is H-projective, and so
is its composite with the structure morphism: over a field the two notions agree (Stacks,
Tag 0B45). -/
private theorem isProjectiveMorphism_of_isProjective {X Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) (hY : IsProjectiveMorphism sY) (g : X ⟶ Y) (hg : IsProjective g) :
    IsProjectiveMorphism (g ≫ sY) ∧ IsProjectiveMorphism g := by
  have hS : HasAmpleInvertibleSheaf (Spec (.of ℂ)) :=
    (hasAmpleInvertibleSheaf_iff _).mpr (Stacks.HProjective.exists_isAmple_of_isAffine _)
  have hsY : IsProjective sY :=
    (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf sY hS).mpr hY
  have hc : IsProjective (g ≫ sY) := isProjective_comp_of_hasAmpleInvertibleSheaf g sY hS hsY hg
  have hcm := (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf _ hS).mp hc
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY hY
  exact ⟨hcm, IsProjectiveMorphism.of_comp g sY hcm⟩

end General

/-! ### Stages of the programme -/

section Stage

variable {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))

/-- A model of the programme over `Z`: a `ℚ`-factorial projective threefold with a canonical
divisor, a boundary and a projective birational morphism to `Z` over `ℂ`. -/
private structure Stage where
  V : Scheme.{0}
  [isIntegral : IsIntegral V]
  [compactSpace : CompactSpace V]
  [isLocallyNoetherian : IsLocallyNoetherian V]
  [isNormal : IsNormal V]
  sV : V ⟶ Spec (.of ℂ)
  K : Divisor V
  Θ : QDivisor V
  π : V ⟶ Z
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ sV
  isQFactorial : MMP.Fourfold.IsQFactorial sV
  dim_eq : topologicalKrullDim V = 3
  isCanonicalDivisor : ∃ n : ℕ, K.IsCanonicalDivisor sV n
  comp_eq : π ≫ sZ = sV
  isProjectiveMorphism : IsProjectiveMorphism π
  isBirationalMorphism : MMP.Mori.IsBirationalMorphism π

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal

variable {sZ}

/-- The adjoint of a stage is nef over the base. -/
private def Stage.IsNef (s : Stage sZ) : Prop :=
  QDivisor.IsRelativelyNef s.sV s.π (Divisor.toQDivisor s.K + s.Θ)

/-- The canonical divisor of a stage is a canonical divisor of dimension three. -/
private theorem Stage.isCanonicalDivisor_three (s : Stage sZ) : s.K.IsCanonicalDivisor s.sV 3 := by
  obtain ⟨n, hn⟩ := s.isCanonicalDivisor
  obtain rfl : n = 3 := by exact_mod_cast hn.topologicalKrullDim_eq.symm.trans s.dim_eq
  exact hn

/-- A step of the programme from the stage `s` to the stage `s'`. -/
private structure IsStep (s s' : Stage sZ) {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℂ))
    (g : s.V ⟶ T) (gp : s'.V ⟶ T) (h : T ⟶ Z) (R : Set (NumericalCurveClasses s.sV)) :
    Prop where
  isThreefoldStepDiagram : IsThreefoldStepDiagram s.sV sT s'.sV s.K s.Θ g gp
  K_eq : s'.K = flipTransform g gp s.K
  Θ_eq : s'.Θ = flipTransform g gp s.Θ
  comp_eq_base : h ≫ sZ = sT
  π_eq : s.π = g ≫ h
  π_eq' : s'.π = gp ≫ h
  isNegativeExtremalRayOf : IsNegativeExtremalRayOf s.sV (Divisor.toQDivisor s.K + s.Θ) R
  exists_ray_eq : ∃ C : ProperCurve s.sV, C.IsContractedBy s.π ∧
    R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u}
  isContractionOfRay : IsContractionOfRay s.sV sT R g
  relativePicardNumber_eq_one : relativePicardNumberN1 s.sV g = 1

/-- The data of a step from `s`, which is a step of the programme when `s` is klt and its adjoint
is not nef over the base. -/
private structure StepData (s : Stage sZ) where
  next : Stage sZ
  T : Scheme.{0}
  sT : T ⟶ Spec (.of ℂ)
  g : s.V ⟶ T
  gp : next.V ⟶ T
  h : T ⟶ Z
  R : Set (NumericalCurveClasses s.sV)
  spec : ¬ s.IsNef → IsKltPair s.sV s.Θ → IsStep s next sT g gp h R

/-- The transform of a canonical divisor along a birational morphism `g : V ⟶ W` of normal
threefolds is a canonical divisor of `W`. -/
private theorem isCanonicalDivisor_flipTransform_id {V W : Scheme.{0}} [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [IsIntegral W] [CompactSpace W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)} {g : V ⟶ W} [IsProper g]
    (hWn : IsNormalVariety ℂ sW) (hVn : IsNormalVariety ℂ (g ≫ sW))
    (hgb : IsBirationalMorphism g) (hdimW : topologicalKrullDim W = 3) {K : Divisor V}
    (hK : K.IsCanonicalDivisor (g ≫ sW) 3) :
    Divisor.IsCanonicalDivisor sW 3 (flipTransform g (𝟙 W) K) := by
  haveI : IsDominant g := hgb.isDominant
  haveI : LocallyOfFiniteType (g ≫ sW) := hVn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sW hWn (n := 3) hdimW
  change Divisor.IsCanonicalDivisor sW 3
    (inverseTransformDivisor (𝟙 W) (RationalMap.transformDivisor g.toRationalMap K))
  rw [inverseTransformDivisor_id]
  exact MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hWn hVn hgb hK₀ hK

/-- **One step of the programme.** At a klt stage whose adjoint is not nef over the base, the
contraction of a negative extremal ray spanned by a curve contracted over the base, followed by
its flip when it is small, is a step of the programme. -/
private theorem exists_isStep (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (s : Stage sZ) (hs : ¬ s.IsNef)
    (hklt : IsKltPair s.sV s.Θ) :
    ∃ (s' : Stage sZ) (T : Scheme.{0}) (sT : T ⟶ Spec (.of ℂ)) (g : s.V ⟶ T) (gp : s'.V ⟶ T)
      (h : T ⟶ Z) (R : Set (NumericalCurveClasses s.sV)), IsStep s s' sT g gp h R := by
  have hKn := s.isCanonicalDivisor_three
  -- the negative extremal ray, its contraction `g : V ⟶ W` and the factorization over `Z`
  obtain ⟨R, hR, ⟨C₀, hC₀, hRC⟩, W, sW, g, hg, hW, hρ, -, hamp, ⟨h, hgh, hhsZ⟩, -⟩ :=
    exists_isContractionOfRay_comp_eq_of_not_isRelativelyNef s.sV s.isProjectiveVariety hklt hKn
      hZ s.comp_eq hs
  have hRπ : ∀ C : ProperCurve s.sV, OneCycle.numericalClass s.sV (C.cycle ℝ) ∈ R →
      C.IsContractedBy s.π := by
    intro C hC x hx
    rw [← hgh, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, (hg.isContractedBy_iff C).2 hC x hx]
  have hRe := hR.choose_spec.1
  have hgb : IsBirationalMorphism g := isBirationalMorphism_of_isContractionOfRay
    s.isProjectiveVariety s.isProjectiveMorphism s.isBirationalMorphism s.comp_eq hRe hRπ hg
  have hWn : IsNormalVariety ℂ sW := hg.isNormalVariety_target
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : IsProper sW := hW.isProjective.isProjective.isProper
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsSeparated sZ := hZ.toIsSeparated
  haveI : IsSeparated sW := hW.toIsSeparated
  haveI : IsProper g := isProper_of_isProjectiveMorphism _ hg.isProjectiveMorphism
  have hhp : IsProjectiveMorphism h := IsProjectiveMorphism.of_comp h sZ (hhsZ ▸ hW.isProjective)
  have hdlt : IsProjectiveQFactorialDltPair s.sV s.K s.Θ :=
    ⟨s.isProjectiveVariety, s.isQFactorial, s.isCanonicalDivisor, isDltPair_of_isKltPair hklt⟩
  have hVn : IsNormalVariety ℂ s.sV := s.isQFactorial.1
  haveI : MMP.Mori.IsVariety ℂ s.sV := hVn.1
  haveI : MMP.Mori.IsVariety ℂ sW := hWn.1
  have hdimW : topologicalKrullDim W = 3 := by
    rw [← s.dim_eq, MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW s.sV hgb]
  have hhb : IsBirationalMorphism h := by
    haveI : IsIntegral Z := hZn.1.toIsIntegral
    haveI : LocallyOfFiniteType (h ≫ sZ) := hhsZ ▸ inferInstance
    haveI : LocallyOfFiniteType h := LocallyOfFiniteType.of_comp (g := sZ) ‹_›
    exact MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left g h hgb
      (hgh ▸ s.isBirationalMorphism)
  -- the step, given its positive side `fp : U' ⟶ W`
  have key : ∀ (U' : Scheme.{0}) [IsIntegral U'] [CompactSpace U'] [IsLocallyNoetherian U']
      [IsNormal U'] (sU' : U' ⟶ Spec (.of ℂ)) (fp : U' ⟶ W),
      IsSmallMorphism sU' sW fp → IsProjectiveMorphism fp →
      IsProjectiveElementaryDltStep s.sV sW sU' s.K s.Θ R g fp (flipTransform g fp s.Θ) →
      MMP.Mori.QDivisor.HasRelativelyAmpleMultiple
        (Divisor.toQDivisor (flipTransform g fp s.K) + flipTransform g fp s.Θ) fp →
      Divisor.IsCanonicalDivisor sU' 3 (flipTransform g fp s.K) →
      ∃ (s' : Stage sZ) (gp : s'.V ⟶ W), IsStep s s' sW g gp h R := by
    intro U' _ _ _ _ sU' fp hfs hfp hstep hampp hKp
    have hU' := hstep.isQFactorial_and_isDltPair
    have hU'n : IsNormalVariety ℂ sU' := hU'.1.1
    haveI : MMP.Mori.IsVariety ℂ sU' := hU'n.1
    haveI : IsProper fp := hfs.isProper
    have hfpb : IsBirationalMorphism fp := hfs.isBirationalMorphism
    have hdimU' : topologicalKrullDim U' = 3 := by
      rw [← hdimW, MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW sU' hfpb]
    have hU'p : MMP.Mori.IsProjectiveVariety ℂ sU' := by
      refine (MMP.Mori.isProjectiveVariety_iff ℂ sU').2 ⟨hU'n.1, ?_⟩
      rw [← hfs.comp_eq]
      exact hfp.comp hW.isProjective
    have hdiag : IsThreefoldStepDiagram s.sV sW sU' s.K s.Θ g fp :=
      { isProjectiveVariety_minus := s.isProjectiveVariety
        isNormalVariety_minus := hVn
        dim_minus := s.dim_eq
        isProjectiveVariety_plus := hU'p
        isNormalVariety_plus := hU'n
        dim_plus := hdimU'
        isProjectiveVariety_target := hW
        isNormalVariety_target := hWn
        comp_eq_minus := hg.comp_eq
        comp_eq_plus := hfs.comp_eq
        isProjectiveMorphism_minus := hg.isProjectiveMorphism
        isProjectiveMorphism_plus := hfp
        isBirationalMorphism_minus := hgb
        isIso_app_minus := hg.isIso_app
        isIso_app_plus := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
          sU' sW hU'n.1 hWn fp hfpb).1
        isSmallMorphism_plus := hfs
        isCanonicalDivisor := s.isCanonicalDivisor
        isCanonicalDivisor_plus := ⟨3, hKp⟩
        nonneg := hklt.1.nonneg
        isQCartier_minus := isQCartier_of_isQFactorial _ s.isQFactorial _
        isQCartier_plus := isQCartier_of_isQFactorial _ hU'.1 _
        hasRelativelyAmpleMultiple_minus := hamp
        hasRelativelyAmpleMultiple_plus := hampp }
    have hπ' : IsProjectiveMorphism (fp ≫ h) := hfp.comp hhp
    let s' : Stage sZ :=
      { V := U'
        sV := sU'
        K := flipTransform g fp s.K
        Θ := flipTransform g fp s.Θ
        π := fp ≫ h
        isProjectiveVariety := hU'p
        isQFactorial := hU'.1
        dim_eq := hdimU'
        isCanonicalDivisor := ⟨3, hKp⟩
        comp_eq := by rw [Category.assoc, hhsZ, hfs.comp_eq]
        isProjectiveMorphism := hπ'
        isBirationalMorphism :=
          MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hfpb hhb }
    exact ⟨s', fp,
      { isThreefoldStepDiagram := hdiag
        K_eq := rfl
        Θ_eq := rfl
        comp_eq_base := hhsZ
        π_eq := hgh.symm
        π_eq' := rfl
        isNegativeExtremalRayOf := hR
        exists_ray_eq := ⟨C₀, hC₀, hRC⟩
        isContractionOfRay := hg
        relativePicardNumber_eq_one := hρ }⟩
  by_cases hsm : IsSmallMorphism s.sV sW g
  · -- the flip
    have hfc : IsFlippingContraction s.sV sW s.K s.Θ g :=
      ⟨hVn, hWn, hg.comp_eq, s.isCanonicalDivisor,
        isQCartier_of_isQFactorial _ s.isQFactorial _, inferInstance, hgb,
        hsm.two_le_codimension, hamp⟩
    obtain ⟨U', _, _, _, sU', fp, hflip⟩ :=
      exists_isFlip_of_isKltPair s.sV s.K s.Θ s.isProjectiveVariety s.dim_eq s.isQFactorial
        s.isCanonicalDivisor hklt sW R g hR hg hfc
    haveI : IsIntegral U' := hflip.isNormalVariety.1.toIsIntegral
    have hfs : IsSmallMorphism sU' sW fp :=
      ⟨hflip.isNormalVariety, hWn, hflip.comp_eq, hflip.isProper, hflip.isBirationalMorphism,
        hflip.two_le_codimension⟩
    have hfp : IsProjectiveMorphism fp :=
      (isProjectiveMorphism_of_isProjective sW hW.isProjective fp hflip.isProjective).2
    have hflipOf : IsFlipOf s.sV sW sU' (Divisor.toQDivisor s.K + s.Θ) g fp :=
      { isQCartier := isQCartier_of_isQFactorial _ s.isQFactorial _
        isContraction := hg.toIsContraction
        isSmallMorphism := hsm
        hasRelativelyAmpleMultiple := hamp
        isSmallMorphism_flip := hfs
        isProjectiveMorphism_flip := hfp
        isQCartier_flip := by
          rw [map_add, flipTransform_toQDivisor]
          exact hflip.isQCartier
        hasRelativelyAmpleMultiple_flip := by
          rw [map_add, flipTransform_toQDivisor]
          exact hflip.hasRelativelyAmpleMultiple }
    obtain ⟨s', gp, hst⟩ := key U' sU' fp hfs hfp
      ⟨hdlt, hR, hg, hgb, hflip.comp_eq, rfl, Or.inl ⟨hsm, hflipOf⟩⟩
      hflip.hasRelativelyAmpleMultiple (hflip.isCanonicalDivisor_flipTransform hKn)
    exact ⟨s', W, sW, g, gp, h, R, hst⟩
  · -- the divisorial contraction: the next model is `W` itself
    have hstep : IsProjectiveElementaryDltStep s.sV sW sW s.K s.Θ R g (𝟙 W)
        (flipTransform g (𝟙 W) s.Θ) :=
      ⟨hdlt, hR, hg, hgb, Category.id_comp _, rfl, Or.inr ⟨hsm, inferInstance⟩⟩
    have hU' := hstep.isQFactorial_and_isDltPair
    have hid : IsProjectiveMorphism (𝟙 W) :=
      IsProjectiveMorphism.of_comp (𝟙 W) sW ((Category.id_comp sW).symm ▸ hW.isProjective)
    obtain ⟨s', gp, hst⟩ := key W sW (𝟙 W) (isSmallMorphism_id hWn) hid hstep
      (hasRelativelyAmpleMultiple_of_isIso _ (isQCartier_of_isQFactorial _ hU'.1 _))
      (isCanonicalDivisor_flipTransform_id hWn (hg.comp_eq ▸ hVn) hgb hdimW (hg.comp_eq ▸ hKn))
    exact ⟨s', W, sW, g, gp, h, R, hst⟩

private theorem nonempty_stepData (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (s : Stage sZ) : Nonempty (StepData s) := by
  by_cases hs : ¬ s.IsNef ∧ IsKltPair s.sV s.Θ
  · obtain ⟨s', T, sT, g, gp, h, R, hst⟩ := exists_isStep hZ hZn s hs.1 hs.2
    exact ⟨⟨s', T, sT, g, gp, h, R, fun _ _ => hst⟩⟩
  · exact ⟨⟨s, s.V, s.sV, 𝟙 _, 𝟙 _, s.π, ∅, fun h h' => absurd ⟨h, h'⟩ hs⟩⟩

end Stage

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal

/-! ### The programme -/

section Program

variable {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
  (hZn : IsNormalVariety ℂ sZ)

/-- The chosen step from a stage. -/
private noncomputable def stepOf (s : Stage sZ) : StepData s :=
  Classical.choice (nonempty_stepData hZ hZn s)

/-- The stages `s_k` of the programme from `s₀`: `s_{k+1}` is the output of the chosen step from
`s_k`. -/
private noncomputable def stages (s₀ : Stage sZ) (k : ℕ) : Stage sZ :=
  Nat.rec (motive := fun _ => Stage sZ) s₀ (fun _ s => (stepOf hZ hZn s).next) k

variable (s₀ : Stage sZ)

/-- The `k`-th chosen step is a step of the programme. -/
private def IsStepAt (k : ℕ) : Prop :=
  IsStep (stages hZ hZn s₀ k) (stages hZ hZn s₀ (k + 1)) (stepOf hZ hZn (stages hZ hZn s₀ k)).sT
    (stepOf hZ hZn (stages hZ hZn s₀ k)).g (stepOf hZ hZn (stages hZ hZn s₀ k)).gp
    (stepOf hZ hZn (stages hZ hZn s₀ k)).h (stepOf hZ hZn (stages hZ hZn s₀ k)).R

/-- The programme from `s₀` made of the first `m` chosen steps, when these are steps. -/
private noncomputable def program (hklt₀ : IsKltPair s₀.sV s₀.Θ) (m : ℕ)
    (hm : ∀ k < m, IsStepAt hZ hZn s₀ k) :
    RelativeThreefoldProgram s₀.sV sZ s₀.π s₀.K s₀.Θ where
  m := m
  Y := fun k => (stages hZ hZn s₀ (k + 1)).V
  sY := fun k => (stages hZ hZn s₀ (k + 1)).sV
  isIntegral := fun _ => inferInstance
  compactSpace := fun _ => inferInstance
  isLocallyNoetherian := fun _ => inferInstance
  isNormal := fun _ => inferInstance
  KY := fun k => (stages hZ hZn s₀ (k + 1)).K
  ΘY := fun k => (stages hZ hZn s₀ (k + 1)).Θ
  πY := fun k => (stages hZ hZn s₀ (k + 1)).π
  T := fun k => (stepOf hZ hZn (stages hZ hZn s₀ k)).T
  sT := fun k => (stepOf hZ hZn (stages hZ hZn s₀ k)).sT
  g := fun k => match k with
    | 0 => (stepOf hZ hZn (stages hZ hZn s₀ 0)).g
    | k + 1 => (stepOf hZ hZn (stages hZ hZn s₀ (k + 1))).g
  gp := fun k => (stepOf hZ hZn (stages hZ hZn s₀ k)).gp
  h := fun k => (stepOf hZ hZn (stages hZ hZn s₀ k)).h
  R := fun k => match k with
    | 0 => (stepOf hZ hZn (stages hZ hZn s₀ 0)).R
    | k + 1 => (stepOf hZ hZn (stages hZ hZn s₀ (k + 1))).R
  isProjectiveVariety_base := hZ
  isNormalVariety_base := hZn
  isProjectiveVariety := s₀.isProjectiveVariety
  dim_eq := s₀.dim_eq
  isKltPair := hklt₀
  isCanonicalDivisor := s₀.isCanonicalDivisor
  comp_eq := s₀.comp_eq
  isQFactorial := fun k _ => by
    rcases k with _ | k
    · exact s₀.isQFactorial
    · exact (stages hZ hZn s₀ (k + 1)).isQFactorial
  isThreefoldStepDiagram := fun k hk => by
    rcases k with _ | k <;> exact (hm _ hk).isThreefoldStepDiagram
  KY_eq := fun k hk => by rcases k with _ | k <;> exact (hm _ hk).K_eq
  ΘY_eq := fun k hk => by rcases k with _ | k <;> exact (hm _ hk).Θ_eq
  comp_eq_base := fun k hk => (hm k hk).comp_eq_base
  modelMap_eq := fun k hk => by rcases k with _ | k <;> exact (hm _ hk).π_eq
  πY_eq := fun k hk => (hm k hk).π_eq'
  isNegativeExtremalRayOf := fun k hk => by
    rcases k with _ | k <;> exact (hm _ hk).isNegativeExtremalRayOf
  exists_ray_eq := fun k hk => by rcases k with _ | k <;> exact (hm _ hk).exists_ray_eq
  isContractionOfRay := fun k hk => by rcases k with _ | k <;> exact (hm _ hk).isContractionOfRay
  relativePicardNumber_eq_one := fun k hk => by
    rcases k with _ | k <;> exact (hm _ hk).relativePicardNumber_eq_one

/-- The hypothesis on all programmes from `s₀` which the construction consumes: every
contraction is small and every model is klt. -/
private def ProgramsAreKltAndSmall : Prop :=
  ∀ P : RelativeThreefoldProgram s₀.sV sZ s₀.π s₀.K s₀.Θ,
    (∀ k < P.m, IsSmallMorphism (modelStr s₀.sV P.sY k) (P.sT k) (P.g k)) ∧
      ∀ k ≤ P.m, IsKltPair (modelStr s₀.sV P.sY k) (P.boundary k)

variable {hZ hZn s₀}

/-- As long as no stage has nef adjoint, the chosen steps are steps of the programme: the stage
reached is klt, being a model of the programme of the steps before it. -/
private theorem isStepAt_of_forall_not_isNef (hklt₀ : IsKltPair s₀.sV s₀.Θ)
    (hP : ProgramsAreKltAndSmall s₀) :
    ∀ m, (∀ k < m, ¬ (stages hZ hZn s₀ k).IsNef) → ∀ k < m, IsStepAt hZ hZn s₀ k
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | m + 1, hne, k, hk => by
    have ih := isStepAt_of_forall_not_isNef hklt₀ hP m fun j hj => hne j (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih k hk
    · have hklt := (hP (program hZ hZn s₀ hklt₀ k ih)).2 k le_rfl
      have hklt' : IsKltPair (stages hZ hZn s₀ k).sV (stages hZ hZn s₀ k).Θ := by
        rcases k with _ | k <;> exact hklt
      exact (stepOf hZ hZn (stages hZ hZn s₀ k)).spec (hne k (Nat.lt_succ_self k)) hklt'

/-- If no stage of the programme had nef adjoint, the chosen steps would be an infinite sequence
of flips of the terminal pair `s₀`. -/
private theorem exists_isNef (hklt₀ : IsKltPair s₀.sV s₀.Θ) (hP : ProgramsAreKltAndSmall s₀)
    (hterm : haveI : LocallyOfFiniteType s₀.sV := s₀.isQFactorial.1.1.toLocallyOfFiniteType
      MMP.Flips.IsTerminalPair s₀.sV 3 s₀.K s₀.Θ) :
    ∃ k, (stages hZ hZn s₀ k).IsNef := by
  by_contra hne
  push Not at hne
  let st := stages hZ hZn s₀
  have hstep : ∀ k, IsStepAt hZ hZn s₀ k := fun k =>
    isStepAt_of_forall_not_isNef hklt₀ hP (k + 1) (fun j _ => hne j) k (Nat.lt_succ_self k)
  have hsmall : ∀ k, IsSmallMorphism (st k).sV (stepOf hZ hZn (st k)).sT
      (stepOf hZ hZn (st k)).g := by
    intro k
    have h := (hP (program hZ hZn s₀ hklt₀ (k + 1) fun j _ => hstep j)).1 k (Nat.lt_succ_self k)
    rcases k with _ | k <;> exact h
  have hV₀ : IsNormalVariety ℂ s₀.sV := s₀.isQFactorial.1
  haveI : LocallyOfFiniteType s₀.sV := s₀.isQFactorial.1.1.toLocallyOfFiniteType
  obtain ⟨S, hS, -⟩ := MMP.Fourfold.exists_sequenceOfFlips_of_isThreefoldStepDiagram ⊤ le_top
    (fun k => (st k).V) (fun k => (st k).sV) (fun k => (st k).K) (fun k => (st k).Θ)
    (fun k => (stepOf hZ hZn (st k)).T) (fun k => (stepOf hZ hZn (st k)).sT)
    (fun k => (stepOf hZ hZn (st k)).g) (fun k => (stepOf hZ hZn (st k)).gp)
    (fun k => (stepOf hZ hZn (st k)).R)
    ⟨hV₀, s₀.isCanonicalDivisor_three, isQCartier_of_isQFactorial _ s₀.isQFactorial _⟩
    (fun k _ => (hstep k).isThreefoldStepDiagram) (fun k _ => (hstep k).K_eq)
    (fun k _ => (hstep k).Θ_eq) (fun k _ => hsmall k)
    (fun k _ => (hstep k).isNegativeExtremalRayOf)
    (fun k _ => (hstep k).exists_ray_eq.elim fun C hC => ⟨C, hC.2⟩)
    (fun k _ => (hstep k).isContractionOfRay)
  have hT' : S.length < ⊤ :=
    MMP.Flips.SequenceOfFlips.terminates_of_isTerminalPair s₀.dim_eq hterm S
  rw [hS] at hT'
  exact lt_irrefl _ hT'

/-- The programme from `s₀`, stopped at its first stage with nef adjoint. -/
private theorem exists_program (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hklt₀ : IsKltPair s₀.sV s₀.Θ)
    (hP : ProgramsAreKltAndSmall s₀)
    (hterm : haveI : LocallyOfFiniteType s₀.sV := s₀.isQFactorial.1.1.toLocallyOfFiniteType
      MMP.Flips.IsTerminalPair s₀.sV 3 s₀.K s₀.Θ) :
    ∃ P : RelativeThreefoldProgram s₀.sV sZ s₀.π s₀.K s₀.Θ,
      QDivisor.IsRelativelyNef (modelStr s₀.sV P.sY P.m) (modelMap s₀.π P.πY P.m)
        (Divisor.toQDivisor (divisorSeq s₀.K P.KY P.m) + P.boundary P.m) := by
  classical
  have hm := exists_isNef (hZ := hZ) (hZn := hZn) hklt₀ hP hterm
  have hmin : ∀ k < Nat.find hm, ¬ (stages hZ hZn s₀ k).IsNef := fun _ => Nat.find_min hm
  let P := program hZ hZn s₀ hklt₀ (Nat.find hm) (isStepAt_of_forall_not_isNef hklt₀ hP _ hmin)
  refine ⟨P, ?_⟩
  have key : ∀ k, (stages hZ hZn s₀ k).IsNef →
      QDivisor.IsRelativelyNef (modelStr s₀.sV P.sY k) (modelMap s₀.π P.πY k)
        (Divisor.toQDivisor (divisorSeq s₀.K P.KY k) + P.boundary k) := by
    intro k hk
    rcases k with _ | k <;> exact hk
  exact key _ (Nat.find_spec hm)

end Program

/-- In the setting of a decreased boundary `Θ'` of a crepant junction `J` of `(X_i, B_i)`
extracting `I_∞ = I(X_i, B_i)` over a stabilized tail `T`, for any canonical divisor `K` of `Y_i`
there is a finite relative threefold programme over `Z_i` (via `f_i ∘ p_i`) from `(Y_i, Θ')` in
which every contraction `g_k`, `k < m`, is small, every model `(V_k, Θ_k)`, `k ≤ m`, is an
effective terminal pair on a projective `ℚ`-factorial threefold, and whose end has
`K_{V_m} + Θ_m` nef over `Z_i`. -/
private theorem solution
    {T : StabilizedTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i))
    {J : CrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') (K : Divisor J.Y)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor (J.p ≫ T.sX i) n) :
    ∃ P : RelativeThreefoldProgram (J.p ≫ T.sX i) (T.sZ i) (J.p ≫ T.f i) K Θ',
      (∀ k < P.m, IsSmallMorphism (modelStr (J.p ≫ T.sX i) P.sY k) (P.sT k) (P.g k)) ∧
      (∀ k ≤ P.m,
        IsKltTerminalPair (modelStr (J.p ≫ T.sX i) P.sY k) (P.boundary k) ∧
        (P.boundary k).IsEffective ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr (J.p ≫ T.sX i) P.sY k) ∧
        IsQFactorial (modelStr (J.p ≫ T.sX i) P.sY k) ∧
        topologicalKrullDim (modelSeq J.Y P.Y k) = 3) ∧
      QDivisor.IsRelativelyNef (modelStr (J.p ≫ T.sX i) P.sY P.m)
        (modelMap (J.p ≫ T.f i) P.πY P.m)
        (Divisor.toQDivisor (divisorSeq K P.KY P.m) + P.boundary P.m) := by
  have hD := T.isThreefoldStepDiagram i
  have hZ := hD.isProjectiveVariety_target
  have hZn := hD.isNormalVariety_target
  have hcomp : (J.p ≫ T.f i) ≫ T.sZ i = J.p ≫ T.sX i := by
    rw [Category.assoc, hD.comp_eq_minus]
  have hY : IsNormalVariety ℂ (J.p ≫ T.sX i) := J.isQFactorial.1
  haveI : LocallyOfFiniteType (J.p ≫ T.sX i) := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated (T.sZ i) := hZ.toIsSeparated
  have hfb : IsBirationalMorphism (T.f i) := hD.isBirationalMorphism_minus
  let s₀ : Stage (T.sZ i) :=
    { V := J.Y
      sV := J.p ≫ T.sX i
      K := K
      Θ := Θ'
      π := J.p ≫ T.f i
      isProjectiveVariety := J.isProjectiveVariety
      isQFactorial := J.isQFactorial
      dim_eq := J.dim_eq
      isCanonicalDivisor := hK
      comp_eq := hcomp
      isProjectiveMorphism :=
        IsProjectiveMorphism.of_comp _ (T.sZ i) (hcomp ▸ J.isProjectiveVariety.isProjective)
      isBirationalMorphism := MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
        J.isBirationalMorphism hfb }
  obtain ⟨hterm, -⟩ := hΘ'.isKltTerminalPair_and_coeff_mem_Ico hI
  have hP : ProgramsAreKltAndSmall s₀ := fun P => by
    obtain ⟨hsmall, -, -, -, -, hmod⟩ := hΘ'.isSmallMorphism_relativeThreefoldProgram hI P
    exact ⟨hsmall, fun k hk => (hmod k hk).2.2.2.1⟩
  have hterm' : haveI : LocallyOfFiniteType s₀.sV := s₀.isQFactorial.1.1.toLocallyOfFiniteType
      MMP.Flips.IsTerminalPair s₀.sV 3 s₀.K s₀.Θ :=
    hterm.isTerminalPair hterm.1.1.nonneg s₀.isCanonicalDivisor_three
  obtain ⟨P, hnef⟩ := exists_program hZ hZn hterm.1 hP hterm'
  obtain ⟨hsmall, -, -, -, -, hmod⟩ := hΘ'.isSmallMorphism_relativeThreefoldProgram hI P
  refine ⟨P, hsmall, fun k hk => ?_, hnef⟩
  obtain ⟨hproj, hdim, hQ, hterm⟩ := hmod k hk
  exact ⟨hterm, hterm.1.1.nonneg, hproj, hQ, hdim⟩

end Proof_lem_mmp_indexc_bridge_program

end

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StabilizedTail

open MMP.Mori

/-- In the setting of a decreased boundary `Θ'` of a crepant junction `J` of `(X_i, B_i)`
extracting `I_∞ = I(X_i, B_i)` over a stabilized tail `T`, for any canonical divisor `K` of `Y_i`
there is a finite relative threefold programme over `Z_i` (via `f_i ∘ p_i`) from `(Y_i, Θ')` in
which every contraction `g_k`, `k < m`, is small, every model `(V_k, Θ_k)`, `k ≤ m`, is an
effective terminal pair on a projective `ℚ`-factorial threefold, and whose end has
`K_{V_m} + Θ_m` nef over `Z_i`. -/
@[mmp "lem_mmp_indexc_bridge_program"]
public theorem IsDecreasedBoundary.exists_relativeThreefoldProgram
    {T : StabilizedTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i))
    {J : CrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') (K : Divisor J.Y)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor (J.p ≫ T.sX i) n) :
    ∃ P : RelativeThreefoldProgram (J.p ≫ T.sX i) (T.sZ i) (J.p ≫ T.f i) K Θ',
      (∀ k < P.m, IsSmallMorphism (modelStr (J.p ≫ T.sX i) P.sY k) (P.sT k) (P.g k)) ∧
      (∀ k ≤ P.m,
        IsKltTerminalPair (modelStr (J.p ≫ T.sX i) P.sY k) (P.boundary k) ∧
        (P.boundary k).IsEffective ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr (J.p ≫ T.sX i) P.sY k) ∧
        IsQFactorial (modelStr (J.p ≫ T.sX i) P.sY k) ∧
        topologicalKrullDim (modelSeq J.Y P.Y k) = 3) ∧
      QDivisor.IsRelativelyNef (modelStr (J.p ≫ T.sX i) P.sY P.m)
        (modelMap (J.p ≫ T.f i) P.πY P.m)
        (Divisor.toQDivisor (divisorSeq K P.KY P.m) + P.boundary P.m) :=
  Proof_lem_mmp_indexc_bridge_program.solution hI hΘ' K hK

end MMP.Fourfold.StabilizedTail
