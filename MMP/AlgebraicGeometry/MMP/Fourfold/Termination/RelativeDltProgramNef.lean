module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltSmallContractionFlip
public import MMP.AlgebraicGeometry.MMP.Contraction.DltRayContraction
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryStepPreserved
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.ElementaryDltTermination
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.LcVerticalNegativeRay
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionLabels
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic

/-!
# A relative dlt program from a crepant dlt lift reaches a nef end

Let `(X, B) → Z ← (X⁺, B⁺)` be a permitted step (`MMP.Fourfold.IsPermittedStep`) of projective
lc fourfold pairs over `ℂ` with rational boundary, and `p : (U, Δ) ⟶ (X, B)` a crepant dlt lift
(`MMP.Fourfold.IsCrepantDltLift`). Then there is an elementary dlt program
`(U^k, Δ^k)_{0 ≤ k ≤ m}` over `Z` from `(U, Δ)` with `h₀ = f ∘ p`
(`MMP.Fourfold.RelativeElementaryDltProgram`) such that `K_{U^m} + Δ^m` is nef over `Z`.

The program is built ray by ray: while `K_{U^k} + Δ^k` is not nef over `Z`, there is a
`(K_{U^k} + Δ^k)`-negative extremal ray of `NE̅(U^k)` all of whose curves are contracted to points
of `Z`; its contraction factors `h_k` and is birational, and the elementary step exists. By
termination of elementary dlt programs of projective `ℚ`-factorial dlt fourfold pairs the
construction stops, necessarily at a model nef over `Z`.

## Main results

* `MMP.Fourfold.IsCrepantDltLift.exists_relativeElementaryDltProgram_isRelativelyNef`: the
  statement above.

## Implementation notes

The models of a program `P` are `U^k = modelSeq U P.Y k`, with structure morphisms
`modelStr (p ≫ s_X) P.sY k`, canonical divisors `divisorSeq K_U P.KY k`, boundaries
`divisorSeq Δ P.ΔY k` and morphisms `h_k = modelMap (p ≫ f) P.hY k` to `Z`; the last index is
`m = P.n.toNat`. The canonical divisor `K_U` of `U` is given: a program records the canonical
divisors of its models, and any canonical divisor of `U` may start it. Nefness over `Z` is
`MMP.Mori.QDivisor.IsRelativelyNef`, which includes that `K_{U^m} + Δ^m` is `ℚ`-Cartier.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace Proof_lem_oai4_c3_dlt_bridge_exists

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Birational and projective morphisms -/

section Morphisms

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- A composite of birational morphisms of integral schemes, locally of finite type, is a
birational morphism. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] {f : X ⟶ Y} {g : Y ⟶ Z} [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) :=
  isBirationalMorphism_of_isBirational _
    ((MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf).comp
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg))

/-- If `g` and `g ≫ h` are birational morphisms of integral schemes and `h` is locally of finite
type, then `h` is a birational morphism. -/
private theorem isBirationalMorphism_of_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (g : X ⟶ Y) (h : Y ⟶ Z) [LocallyOfFiniteType h]
    (hg : IsBirationalMorphism g) (hgh : IsBirationalMorphism (g ≫ h)) :
    IsBirationalMorphism h := by
  have hgS := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg
  have hghS := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hgh
  haveI := hg.isDominant
  haveI := hgh.isDominant
  haveI : IsDominant h := IsDominant.of_comp g h
  refine isBirationalMorphism_of_isBirational h ⟨?_, fun x hx => ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton,
      ← map_genericPoint_of_isDominant h]
    exact Set.bijOn_singleton.mpr rfl
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    have h1 := hghS.isIso_stalkMap (genericPoint X) (by simp [genericPoints_eq_singleton])
    have h2 := hgS.isIso_stalkMap (genericPoint X) (by simp [genericPoints_eq_singleton])
    rw [Scheme.Hom.stalkMap_comp] at h1
    have h3 : IsIso (h.stalkMap (g (genericPoint X))) :=
      @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h2 h1
    have hη : g (genericPoint X) = genericPoint Y := map_genericPoint_of_isDominant g
    revert h3
    generalize g (genericPoint X) = y at hη
    subst hη
    exact id

/-- A scheme projective over a projective variety is a projective variety. -/
private theorem isProjectiveVariety_comp {k : Type} [Field k] {X U : Scheme.{0}} [IsIntegral U]
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsProjectiveVariety k sX) {p : U ⟶ X}
    (hp : IsProjectiveMorphism p) : MMP.Mori.IsProjectiveVariety k (p ≫ sX) := by
  have hproj : IsProjectiveMorphism (p ≫ sX) := hp.comp hX.isProjective
  haveI := isProper_of_isProjectiveMorphism _ hproj
  exact { toIsVariety := ⟨⟩, isProjective := hproj }

end Morphisms

section Stage

variable {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))

/-- A model of the program over `Z`: a projective `ℚ`-factorial dlt fourfold pair over `ℂ`
with a projective birational morphism to `Z` over `ℂ`. -/
private structure Stage where
  W : Scheme.{0}
  [isIntegral : IsIntegral W]
  [compactSpace : CompactSpace W]
  [isLocallyNoetherian : IsLocallyNoetherian W]
  [isNormal : IsNormal W]
  sW : W ⟶ Spec (.of ℂ)
  K : Divisor W
  Δ : QDivisor W
  h : W ⟶ Z
  isProjectiveQFactorialDltPair : IsProjectiveQFactorialDltPair sW K Δ
  dim_eq : topologicalKrullDim W = 4
  isProjectiveMorphism : IsProjectiveMorphism h
  comp_eq : h ≫ sZ = sW
  isBirationalMorphism : IsBirationalMorphism h

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal

variable {sZ}

/-- The adjoint of a stage is nef over the base. -/
private def Stage.IsNef (s : Stage sZ) : Prop :=
  QDivisor.IsRelativelyNef s.sW s.h (Divisor.toQDivisor s.K + s.Δ)

/-- The data of a step from `s`, which is an elementary step over `Z` when the adjoint of `s`
is not nef over the base. -/
private structure StepData (s : Stage sZ) where
  next : Stage sZ
  V : Scheme.{0}
  sV : V ⟶ Spec (.of ℂ)
  g : s.W ⟶ V
  fp : next.W ⟶ V
  hV : V ⟶ Z
  R : Set (NumericalCurveClasses s.sW)
  spec : ¬ s.IsNef →
    IsProjectiveElementaryDltStep s.sW sV next.sW s.K s.Δ R g fp next.Δ ∧
      g ≫ hV = s.h ∧ next.h = fp ≫ hV

/-- **One step of the program.** -/
private theorem exists_step (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (s : Stage sZ)
    (hs : ¬ s.IsNef) :
    ∃ (s' : Stage sZ) (V : Scheme.{0}) (sV : V ⟶ Spec (.of ℂ)) (g : s.W ⟶ V) (fp : s'.W ⟶ V)
      (hV : V ⟶ Z) (R : Set (NumericalCurveClasses s.sW)),
      IsProjectiveElementaryDltStep s.sW sV s'.sW s.K s.Δ R g fp s'.Δ ∧
        g ≫ hV = s.h ∧ s'.h = fp ≫ hV := by
  have hU := s.isProjectiveQFactorialDltPair
  haveI := hU.isProjectiveVariety.toIsVariety
  haveI := hZ.toIsVariety
  obtain ⟨R, hR, hRh⟩ := exists_isNegativeExtremalRayOf_isContractedBy_of_not_isRelativelyNef
    hU.isProjectiveVariety hZ hU.isCanonicalDivisor hU.isDltPair.1 s.isProjectiveMorphism
    s.comp_eq hs
  obtain ⟨V, sV, g, hg, hV, hρ, hamp⟩ := hU.exists_isContractionOfRay hR
  obtain ⟨-, hext, -⟩ := id hR
  obtain ⟨h', hh', -⟩ := existsUnique_comp_eq_of_isContractionOfRay hU.isProjectiveVariety
    s.isProjectiveMorphism s.comp_eq hext hRh hg
  have hgb := isBirationalMorphism_of_isContractionOfRay hU.isProjectiveVariety
    s.isProjectiveMorphism s.isBirationalMorphism s.comp_eq hext hRh hg
  -- the target `V` is a normal projective variety
  obtain ⟨hVv, hVn⟩ := hg.isNormalVariety_target
  haveI := hVv
  haveI := hVv.toIsIntegral
  haveI : IsNormal V := hVn
  haveI := hV.toIsVariety
  haveI : IsProper sV := isProper_of_isProjectiveMorphism _ hV.isProjective
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism _ hZ.isProjective
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  -- `h' : V ⟶ Z` lies over `ℂ`, is projective and birational
  have hsV : h' ≫ sZ = sV := by
    obtain ⟨_, -, huniq⟩ := existsUnique_comp_eq_of_isContractionOfRay (sZ := 𝟙 _)
      hU.isProjectiveVariety hU.isProjectiveVariety.isProjective (Category.comp_id _) hext
      (fun _ _ _ _ => Subsingleton.elim _ _) hg
    rw [huniq sV hg.comp_eq, huniq (h' ≫ sZ) (by
      show g ≫ h' ≫ sZ = s.sW; rw [← Category.assoc, hh', s.comp_eq])]
  haveI : IsProper (h' ≫ sZ) := hsV ▸ inferInstance
  haveI : IsProper h' := IsProper.of_comp h' sZ
  have hh'p : IsProjectiveMorphism h' := by
    haveI := IsProjectiveVariety.isQuasiProjectiveVariety ℂ sV
    exact MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sV sZ h' hsV
  haveI := hZ.toIsVariety.toIsIntegral
  have hh'b : IsBirationalMorphism h' := isBirationalMorphism_of_comp g h' hgb (hh' ▸ s.isBirationalMorphism)
  by_cases hsm : IsSmallMorphism s.sW sV g
  · -- the small case: the flip
    obtain ⟨U', _, _, _, _, sU', fp, hfp, hflip, hU'⟩ :=
      hU.exists_isFlipOf_of_isSmallMorphism s.dim_eq hR hg hsm hV hρ hamp
    haveI := hU'.isProjectiveVariety.toIsVariety
    have hfpb := hflip.isSmallMorphism_flip.isBirationalMorphism
    haveI := isProper_of_isProjectiveMorphism _ hflip.isProjectiveMorphism_flip
    refine ⟨⟨U', sU', flipTransform g fp s.K, flipTransform g fp s.Δ, fp ≫ h', hU', ?_,
      hflip.isProjectiveMorphism_flip.comp hh'p, by rw [Category.assoc, hsV, hfp],
      isBirationalMorphism_comp hfpb hh'b⟩, V, sV, g, fp, h', R,
      ⟨hU, hR, hg, hgb, hfp, rfl, Or.inl ⟨hsm, hflip⟩⟩, hh', rfl⟩
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV sU' hfpb,
      MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV s.sW hgb, s.dim_eq]
  · -- the divisorial case: the contraction itself
    have hst : IsProjectiveElementaryDltStep s.sW sV sV s.K s.Δ R g (𝟙 V)
        (flipTransform g (𝟙 V) s.Δ) :=
      ⟨hU, hR, hg, hgb, Category.id_comp _, rfl, Or.inr ⟨hsm, inferInstance⟩⟩
    refine ⟨⟨V, sV, flipTransform g (𝟙 V) s.K, flipTransform g (𝟙 V) s.Δ, 𝟙 V ≫ h',
      hst.isProjectiveQFactorialDltPair_flipTransform hV hρ hamp, ?_,
      by rw [Category.id_comp]; exact hh'p, by rw [Category.id_comp, hsV],
      by rw [Category.id_comp]; exact hh'b⟩, V, sV, g, 𝟙 V, h', R, hst, hh', rfl⟩
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV s.sW hgb, s.dim_eq]

private theorem nonempty_stepData (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (s : Stage sZ) :
    Nonempty (StepData s) := by
  by_cases hs : s.IsNef
  · exact ⟨⟨s, s.W, s.sW, 𝟙 _, 𝟙 _, s.h, ∅, fun h => absurd hs h⟩⟩
  · obtain ⟨s', V, sV, g, fp, hV, R, hst⟩ := exists_step hZ s hs
    exact ⟨⟨s', V, sV, g, fp, hV, R, fun _ => hst⟩⟩

end Stage

/-! ### The program -/

section Program

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal

variable {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)

/-- The chosen step at a stage. -/
private noncomputable def step (s : Stage sZ) : StepData s := (nonempty_stepData hZ s).some

/-- The stages of the program from `s₀`, obtained by iterating the chosen steps. -/
private noncomputable def stages (s₀ : Stage sZ) : ℕ → Stage sZ
  | 0 => s₀
  | j + 1 => (step hZ (stages s₀ j)).next

/-- The elementary dlt program over `Z` of length `n` along the stages from `s₀`, when the stages
`j < n` are not nef over the base. -/
private noncomputable def toProgram (s₀ : Stage sZ) (n : ℕ∞)
    (hn : ∀ j : ℕ, (j : ℕ∞) < n → ¬ (stages hZ s₀ j).IsNef) :
    ElementaryDltProgram s₀.sW s₀.K s₀.Δ where
  n := n
  Y j := (stages hZ s₀ (j + 1)).W
  sY j := (stages hZ s₀ (j + 1)).sW
  KY j := (stages hZ s₀ (j + 1)).K
  ΔY j := (stages hZ s₀ (j + 1)).Δ
  R j := match j with
    | 0 => (step hZ (stages hZ s₀ 0)).R
    | j + 1 => (step hZ (stages hZ s₀ (j + 1))).R
  V j := (step hZ (stages hZ s₀ j)).V
  sV j := (step hZ (stages hZ s₀ j)).sV
  f j := match j with
    | 0 => (step hZ (stages hZ s₀ 0)).g
    | j + 1 => (step hZ (stages hZ s₀ (j + 1))).g
  fp j := (step hZ (stages hZ s₀ j)).fp
  isProjectiveQFactorialDltPair j _ := by
    cases j with
    | zero => exact (stages hZ s₀ 0).isProjectiveQFactorialDltPair
    | succ j => exact (stages hZ s₀ (j + 1)).isProjectiveQFactorialDltPair
  isProjectiveElementaryDltStep j hj := by
    cases j <;> exact ((step hZ (stages hZ s₀ _)).spec (hn _ hj)).1

/-- The program `toProgram` is over `Z`, with `h_j` the morphisms of the stages. -/
private noncomputable def toRelativeProgram (s₀ : Stage sZ) (n : ℕ)
    (hn : ∀ j : ℕ, (j : ℕ∞) < n → ¬ (stages hZ s₀ j).IsNef) :
    RelativeElementaryDltProgram s₀.sW s₀.K s₀.Δ s₀.h where
  toElementaryDltProgram := toProgram hZ s₀ n hn
  n_ne_top := ENat.coe_ne_top n
  hY j := (stages hZ s₀ (j + 1)).h
  hV j := (step hZ (stages hZ s₀ j)).hV
  isProjectiveMorphism j _ := by
    cases j with
    | zero => exact (stages hZ s₀ 0).isProjectiveMorphism
    | succ j => exact (stages hZ s₀ (j + 1)).isProjectiveMorphism
  comp_hV j hj := by
    cases j <;> exact ((step hZ (stages hZ s₀ _)).spec (hn _ hj)).2.1
  hY_eq j hj := ((step hZ (stages hZ s₀ j)).spec (hn _ hj)).2.2

/-- **The stages reach a nef model.** Otherwise they form an infinite elementary dlt program. -/
private theorem exists_isNef (s₀ : Stage sZ) : ∃ m, (stages hZ s₀ m).IsNef := by
  by_contra hne
  push Not at hne
  exact ElementaryDltProgram.n_ne_top s₀.dim_eq (toProgram hZ s₀ ⊤ fun j _ => hne j) rfl

include hZ in
/-- From any stage there is an elementary dlt program over `Z` ending nef over `Z`. -/
private theorem exists_relativeElementaryDltProgram (s₀ : Stage sZ) :
    ∃ P : RelativeElementaryDltProgram s₀.sW s₀.K s₀.Δ s₀.h,
      QDivisor.IsRelativelyNef (modelStr s₀.sW P.sY P.n.toNat) (modelMap s₀.h P.hY P.n.toNat)
        (Divisor.toQDivisor (divisorSeq s₀.K P.KY P.n.toNat) +
          divisorSeq s₀.Δ P.ΔY P.n.toNat) := by
  classical
  have hex := exists_isNef hZ s₀
  refine ⟨toRelativeProgram hZ s₀ (Nat.find hex)
    (fun j hj => Nat.find_min hex (by exact_mod_cast hj)), ?_⟩
  have key : ∀ j, (stages hZ s₀ j).IsNef →
      QDivisor.IsRelativelyNef (modelStr s₀.sW (fun i => (stages hZ s₀ (i + 1)).sW) j)
        (modelMap s₀.h (fun i => (stages hZ s₀ (i + 1)).h) j)
        (Divisor.toQDivisor (divisorSeq s₀.K (fun i => (stages hZ s₀ (i + 1)).K) j) +
          divisorSeq s₀.Δ (fun i => (stages hZ s₀ (i + 1)).Δ) j) := by
    intro j hj
    cases j <;> exact hj
  refine key _ ?_
  rw [show (toRelativeProgram hZ s₀ (Nat.find hex) _).n.toNat = Nat.find hex from
    ENat.toNat_coe _]
  exact Nat.find_spec hex

end Program

/-! ### The initial stage -/

section Initial

variable {X X' Z U : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}
    {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- The crepant dlt lift, with its morphism to `Z`, is a stage. -/
private noncomputable def initialStage (hstep : IsPermittedStep sX sZ sX' K B R f fp)
    (hdim : topologicalKrullDim X = 4)
    {p : U ⟶ X} {Δ : QDivisor U} (hp : IsCrepantDltLift sX K B p Δ)
    {KU : Divisor U} (hKU : ∃ n : ℕ, KU.IsCanonicalDivisor (p ≫ sX) n) : Stage sZ where
  W := U
  sW := p ≫ sX
  K := KU
  Δ := Δ
  h := p ≫ f
  isProjectiveQFactorialDltPair :=
    ⟨isProjectiveVariety_comp hp.isProjectiveVariety hp.isProjectiveMorphism, hp.isQFactorial, hKU,
      hp.isDltPair⟩
  dim_eq := by
    haveI := hp.isProjectiveVariety.toIsVariety
    haveI := (isProjectiveVariety_comp hp.isProjectiveVariety hp.isProjectiveMorphism).toIsVariety
    rw [← hdim]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX)
      hp.isBirationalMorphism).symm
  isProjectiveMorphism := hp.isProjectiveMorphism.comp hstep.isContractionOfRay.isProjectiveMorphism
  comp_eq := by rw [Category.assoc, hstep.isContractionOfRay.comp_eq]
  isBirationalMorphism := by
    haveI := hstep.isContractionOfRay.isNormalVariety_target.1.toIsIntegral
    haveI := isProper_of_isProjectiveMorphism _ hp.isProjectiveMorphism
    haveI := isProper_of_isProjectiveMorphism _ hstep.isContractionOfRay.isProjectiveMorphism
    exact isBirationalMorphism_comp hp.isBirationalMorphism hstep.isBirationalMorphism

end Initial

private theorem solution
    {X X' Z U : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}
    {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hstep : IsPermittedStep sX sZ sX' K B R f fp)
    (hdim : topologicalKrullDim X = 4) (hdim' : topologicalKrullDim X' = 4)
    {p : U ⟶ X} {Δ : QDivisor U} (hp : IsCrepantDltLift sX K B p Δ)
    {KU : Divisor U} (hKU : ∃ n : ℕ, KU.IsCanonicalDivisor (p ≫ sX) n) :
    ∃ P : RelativeElementaryDltProgram (p ≫ sX) KU Δ (p ≫ f),
      QDivisor.IsRelativelyNef (modelStr (p ≫ sX) P.sY P.n.toNat)
        (modelMap (p ≫ f) P.hY P.n.toNat)
        (Divisor.toQDivisor (divisorSeq KU P.KY P.n.toNat) + divisorSeq Δ P.ΔY P.n.toNat) :=
  exists_relativeElementaryDltProgram hstep.isProjectiveVariety_target
    (initialStage hstep hdim hp hKU)

end

end Proof_lem_oai4_c3_dlt_bridge_exists

end

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

namespace MMP.Fourfold

/-- **A relative dlt program reaches a nef end.** Let `(X, B) → Z ← (X⁺, B⁺)` be a permitted step
of projective lc fourfold pairs over `ℂ`, with contraction `f : X ⟶ Z`, and let
`p : (U, Δ) ⟶ (X, B)` be a crepant dlt lift, with `K_U` a canonical divisor of `U`. Then there is
an elementary dlt program `P` over `Z` from `(U, Δ)` with `h₀ = p ≫ f` whose last pair
`(U^m, Δ^m)` has `K_{U^m} + Δ^m` nef over `Z` (relative to `h_m : U^m ⟶ Z`). -/
@[mmp "lem_oai4_c3_dlt_bridge_exists"]
public theorem IsCrepantDltLift.exists_relativeElementaryDltProgram_isRelativelyNef
    {X X' Z U : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}
    {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hstep : IsPermittedStep sX sZ sX' K B R f fp)
    (hdim : topologicalKrullDim X = 4) (hdim' : topologicalKrullDim X' = 4)
    {p : U ⟶ X} {Δ : QDivisor U} (hp : IsCrepantDltLift sX K B p Δ)
    {KU : Divisor U} (hKU : ∃ n : ℕ, KU.IsCanonicalDivisor (p ≫ sX) n) :
    ∃ P : RelativeElementaryDltProgram (p ≫ sX) KU Δ (p ≫ f),
      QDivisor.IsRelativelyNef (modelStr (p ≫ sX) P.sY P.n.toNat)
        (modelMap (p ≫ f) P.hY P.n.toNat)
        (Divisor.toQDivisor (divisorSeq KU P.KY P.n.toNat) + divisorSeq Δ P.ΔY P.n.toNat) :=
          by revert X X' Z U sX sZ sX' K B R f fp hstep hdim hdim' p Δ hp KU hKU; first | exact Proof_lem_oai4_c3_dlt_bridge_exists.solution | exact Proof_lem_oai4_c3_dlt_bridge_exists.solution _ | exact Proof_lem_oai4_c3_dlt_bridge_exists.solution _ _ | exact Proof_lem_oai4_c3_dlt_bridge_exists.solution _ _ _ | exact Proof_lem_oai4_c3_dlt_bridge_exists.solution _ _ _ _

end MMP.Fourfold

