module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.AlgClosed.RayContinuable
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.BridgeRelativeProgram
public import MMP.AlgebraicGeometry.Positivity.RelativeNefBaseTwist
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.SurfaceContractionNullFace

/-!
# Maximal programs exist for projective lc fourfolds

Let `(X, B)` be a projective lc pair over `ℂ` of dimension four, with canonical divisor `K`.
Running the program — as long as `K_i + B_i` is not nef, choose a `(K_i + B_i)`-negative
extremal ray, contract it, and either continue with a permitted step when the contraction is
birational or stop with a final fibre-type ray — gives a maximal program from `(X, B)`.

## Main results

* `MMP.Fourfold.exists_program_isMaximal`: a maximal program exists.

## Implementation notes

The program is built by recursion over `ℕ`: every stage is a projective lc fourfold pair with a
canonical divisor, and a permitted step is taken whenever one exists. The number of steps is the
first stage at which no permitted step exists, or `⊤` if there is none. At that stage the adjoint
divisor is nef, or a negative extremal ray exists; the contraction of such a ray is then not
birational, so it is of fibre type. A negative extremal ray exists as soon as the adjoint divisor
is negative on a curve, since `NE̅(X)` is a closed cone on which an ample form is positive.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_exists_program_isMaximal

open MMP.Mori MMP.Fourfold

/-! ### Dimension along dominant morphisms -/

/-- A contraction that is not birational is of fibre type. -/
private theorem topologicalKrullDim_lt_of_not_isBirationalMorphism {k : Type} [Field k]
    {X T : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} {g : X ⟶ T}
    (hg : IsContraction sX sT g) (hbir : ¬ IsBirationalMorphism g) :
    topologicalKrullDim T < topologicalKrullDim X := by
  have hXv : MMP.Mori.IsVariety k sX := hg.isNormalVariety_source.1
  have hTv : MMP.Mori.IsVariety k sT := hg.isNormalVariety_target.1
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsIntegral T := hTv.toIsIntegral
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  haveI : IsDominant g := ⟨hg.surjective.denseRange⟩
  refine lt_of_le_of_ne (Proof_lem_oai4_c1_bridge_mmp.topologicalKrullDim_le_of_isDominant g
    hg.comp_eq) fun h => hbir ?_
  exact hg.isBirationalMorphism_of_topologicalKrullDim_eq h.symm

/-! ### Stages and steps -/

/-- A stage of the program: a projective lc fourfold pair over `ℂ` with a canonical divisor. -/
private structure Stage where
  X : Scheme.{0}
  [isIntegral : IsIntegral X]
  [compactSpace : CompactSpace X]
  [isLocallyNoetherian : IsLocallyNoetherian X]
  [isNormal : IsNormal X]
  sX : X ⟶ Spec (.of ℂ)
  K : Divisor X
  B : QDivisor X
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ sX
  isLogCanonicalPair : MMP.Intersection.IsLogCanonicalPair sX B
  isCanonicalDivisor : ∃ m : ℕ, K.IsCanonicalDivisor sX m
  dim_eq : topologicalKrullDim X = 4

attribute [instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian Stage.isNormal

/-- The data of a step from a stage. -/
private structure StepCand (s : Stage) where
  R : Set (NumericalCurveClasses s.sX)
  Z : Scheme.{0}
  sZ : Z ⟶ Spec (.of ℂ)
  f : s.X ⟶ Z
  next : Stage
  fp : next.X ⟶ Z

/-- A step is a permitted step, with the strict transforms as canonical divisor and boundary. -/
private def StepCand.Good {s : Stage} (d : StepCand s) : Prop :=
  IsPermittedStep s.sX d.sZ d.next.sX s.K s.B d.R d.f d.fp ∧
    d.next.K = flipTransform d.f d.fp s.K ∧ d.next.B = flipTransform d.f d.fp s.B

/-- Whether a stage admits a permitted step. -/
private def Stage.HasStep (s : Stage) : Prop := ∃ d : StepCand s, d.Good

open Classical in
/-- The chosen step of a stage (a trivial one when there is no permitted step). -/
private def Stage.chosen (s : Stage) : StepCand s :=
  if h : s.HasStep then h.choose else ⟨∅, s.X, s.sX, 𝟙 _, s, 𝟙 _⟩

private theorem Stage.chosen_good {s : Stage} (h : s.HasStep) : s.chosen.Good := by
  unfold Stage.chosen
  rw [dif_pos h]
  exact h.choose_spec

/-- A final fibre-type ray of a pair: the conditions of `MMP.Fourfold.Program.final_spec`. -/
private def IsFinal {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (K : Divisor X) (B : QDivisor X)
    (R : Set (NumericalCurveClasses sX)) {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℂ)) (g : X ⟶ T) :
    Prop :=
  IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R ∧ IsContractionOfRay sX sT R g ∧
    MMP.Mori.IsProjectiveVariety ℂ sT ∧ relativePicardNumberN1 sX g = 1 ∧
    (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple g ∧
    topologicalKrullDim T < topologicalKrullDim X

/-- The data of a final contraction. -/
private structure FinalCand {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) where
  R : Set (NumericalCurveClasses sX)
  T : Scheme.{0}
  sT : T ⟶ Spec (.of ℂ)
  g : X ⟶ T

/-- **One step of the program.** At a stage, the adjoint divisor is nef, or there is a permitted
step, or there is a final fibre-type ray. -/
private theorem Stage.trichotomy (s : Stage) :
    QDivisor.IsNefOnCurves s.sX (Divisor.toQDivisor s.K + s.B) ∨ s.HasStep ∨
      ∃ c : FinalCand s.sX, IsFinal s.sX s.K s.B c.R c.sT c.g := by
  have hproj := s.isProjectiveVariety
  have hlc := s.isLogCanonicalPair
  have hK := s.isCanonicalDivisor
  have hdim := s.dim_eq
  have hQ := Proof_lem_oai4_finite_existence_transfer_b.isQCartier_of_isLogCanonicalPair hlc hK
  by_cases hnef : QDivisor.IsNefOnCurves s.sX (Divisor.toQDivisor s.K + s.B)
  · exact Or.inl hnef
  right
  have hneg : ∃ T : ProperCurve s.sX, QDivisor.curveForm s.sX (Divisor.toQDivisor s.K + s.B) hQ
      (OneCycle.numericalClass s.sX (T.cycle ℝ)) < 0 := by
    by_contra! h
    exact hnef ⟨hQ, h⟩
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ s.sX := hproj
  obtain ⟨R, hRe, hRneg⟩ :=
    MMP.FourfoldProofs.FourfoldKltRelativeNefGlobalBaseTwistProof.exists_isExtremalRay_neg s.sX _
      hneg
  have hR : IsNegativeExtremalRayOf s.sX (Divisor.toQDivisor s.K + s.B) R := ⟨hQ, hRe, hRneg⟩
  obtain ⟨Z, sZ, f, hf, hZ, hρ, hamp⟩ :=
    exists_isContractionOfRay_of_isNegativeExtremalRayOf_of_isAlgClosed hproj hlc hK hdim hR
  by_cases hbir : IsBirationalMorphism f
  · left
    obtain ⟨Xp, _, _, _, _, sXp, fp, hs⟩ :=
      hf.exists_isPermittedStep_of_isAlgClosed hproj hdim hlc hK hR hbir
    have hsm := hs.isSmallMorphism_step
    haveI : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
    obtain ⟨m, hKm⟩ := hK
    have hdimp : topologicalKrullDim Xp = 4 := by
      haveI : MMP.Mori.IsVariety ℂ sZ := hsm.isNormalVariety_target.1
      haveI : MMP.Mori.IsVariety ℂ sXp := hsm.isNormalVariety_source.1
      haveI : MMP.Mori.IsVariety ℂ s.sX := hf.isNormalVariety_source.1
      rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sXp
          hsm.isBirationalMorphism,
        MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ s.sX hbir, hdim]
    let t : Stage :=
      { X := Xp, sX := sXp, K := flipTransform f fp s.K, B := flipTransform f fp s.B
        isProjectiveVariety := hs.isProjectiveVariety_step
        isLogCanonicalPair := hs.isLogCanonicalPair_step
        isCanonicalDivisor := ⟨m, Proof_thm_oai4_main_i.isCanonicalDivisor_flipTransform
          hf.isNormalVariety_source hf.comp_eq hbir hsm hKm⟩
        dim_eq := hdimp }
    exact ⟨⟨R, Z, sZ, f, t, fp⟩, hs, rfl, rfl⟩
  · right
    exact ⟨⟨R, Z, sZ, f⟩, hR, hf, hZ, hρ, hamp,
      topologicalKrullDim_lt_of_not_isBirationalMorphism hf.toIsContraction hbir⟩

/-! ### The program -/

/-- The stages of the program from `s`. -/
private def stages (s : Stage) (i : ℕ) : Stage :=
  Nat.rec (motive := fun _ => Stage) s (fun _ t => t.chosen.next) i

/-- The models after the first. -/
private abbrev pY (s : Stage) (i : ℕ) : Scheme.{0} := (stages s (i + 1)).X

/-- Their structure morphisms. -/
private abbrev psY (s : Stage) (i : ℕ) : pY s i ⟶ Spec (.of ℂ) := (stages s (i + 1)).sX

open Classical in
/-- The number of steps: the first stage without a permitted step. -/
private def pN (s : Stage) : ℕ∞ :=
  if h : ∃ i, ¬ (stages s i).HasStep then (Nat.find h : ℕ∞) else ⊤

private theorem hasStep_of_lt (s : Stage) {i : ℕ} (hi : (i : ℕ∞) < pN s) :
    (stages s i).HasStep := by
  classical
  unfold pN at hi
  split_ifs at hi with h
  · by_contra hc
    exact absurd (Nat.find_min' h hc) (not_le.mpr (by exact_mod_cast hi))
  · exact not_not.mp (not_exists.mp h i)

open Classical in
/-- The final contraction (a trivial one when there is no final fibre-type ray). -/
private def pFinal (s : Stage) : FinalCand (modelStr s.sX (psY s) (pN s).toNat) :=
  if h : ∃ c : FinalCand (modelStr s.sX (psY s) (pN s).toNat),
      IsFinal (modelStr s.sX (psY s) (pN s).toNat)
        (divisorSeq s.K (fun i => (stages s (i + 1)).K) (pN s).toNat)
        (divisorSeq s.B (fun i => (stages s (i + 1)).B) (pN s).toNat) c.R c.sT c.g
  then h.choose else ⟨∅, _, modelStr s.sX (psY s) (pN s).toNat, 𝟙 _⟩

private theorem pFinal_spec (s : Stage)
    (h : ∃ c : FinalCand (modelStr s.sX (psY s) (pN s).toNat),
      IsFinal (modelStr s.sX (psY s) (pN s).toNat)
        (divisorSeq s.K (fun i => (stages s (i + 1)).K) (pN s).toNat)
        (divisorSeq s.B (fun i => (stages s (i + 1)).B) (pN s).toNat) c.R c.sT c.g) :
    IsFinal (modelStr s.sX (psY s) (pN s).toNat)
      (divisorSeq s.K (fun i => (stages s (i + 1)).K) (pN s).toNat)
      (divisorSeq s.B (fun i => (stages s (i + 1)).B) (pN s).toNat)
      (pFinal s).R (pFinal s).sT (pFinal s).g := by
  unfold pFinal
  rw [dif_pos h]
  exact h.choose_spec

/-- The program from `s` taking the chosen permitted step at every stage that has one. -/
private def program (s : Stage) : Program s.sX s.K s.B where
  n := pN s
  Y := pY s
  sY := psY s
  isIntegral i := (stages s (i + 1)).isIntegral
  compactSpace i := (stages s (i + 1)).compactSpace
  isLocallyNoetherian i := (stages s (i + 1)).isLocallyNoetherian
  isNormal i := (stages s (i + 1)).isNormal
  KY i := (stages s (i + 1)).K
  BY i := (stages s (i + 1)).B
  R
    | 0 => (stages s 0).chosen.R
    | j + 1 => (stages s (j + 1)).chosen.R
  Z i := (stages s i).chosen.Z
  sZ i := (stages s i).chosen.sZ
  f
    | 0 => (stages s 0).chosen.f
    | j + 1 => (stages s (j + 1)).chosen.f
  fp i := (stages s i).chosen.fp
  isProjectiveVariety := s.isProjectiveVariety
  isLogCanonicalPair := s.isLogCanonicalPair
  isCanonicalDivisor := s.isCanonicalDivisor
  isPermittedStep
    | 0, hi => (Stage.chosen_good (hasStep_of_lt s hi)).1
    | j + 1, hi => (Stage.chosen_good (hasStep_of_lt s hi)).1
  KY_eq
    | 0, hi => (Stage.chosen_good (hasStep_of_lt s hi)).2.1
    | j + 1, hi => (Stage.chosen_good (hasStep_of_lt s hi)).2.1
  BY_eq
    | 0, hi => (Stage.chosen_good (hasStep_of_lt s hi)).2.2
    | j + 1, hi => (Stage.chosen_good (hasStep_of_lt s hi)).2.2
  hasFinal := pN s ≠ ⊤ ∧ ∃ c : FinalCand (modelStr s.sX (psY s) (pN s).toNat),
      IsFinal (modelStr s.sX (psY s) (pN s).toNat)
        (divisorSeq s.K (fun i => (stages s (i + 1)).K) (pN s).toNat)
        (divisorSeq s.B (fun i => (stages s (i + 1)).B) (pN s).toNat) c.R c.sT c.g
  finalRay := (pFinal s).R
  T := (pFinal s).T
  sT := (pFinal s).sT
  g := (pFinal s).g
  final_spec h := ⟨h.1, pFinal_spec s h.2⟩

/-- The trichotomy at stage `m`, read on the models of the program. -/
private theorem trichotomy_modelSeq (s : Stage) (m : ℕ) :
    QDivisor.IsNefOnCurves (modelStr s.sX (psY s) m)
        (Divisor.toQDivisor (divisorSeq s.K (fun i => (stages s (i + 1)).K) m) +
          divisorSeq s.B (fun i => (stages s (i + 1)).B) m) ∨ (stages s m).HasStep ∨
      ∃ c : FinalCand (modelStr s.sX (psY s) m),
        IsFinal (modelStr s.sX (psY s) m)
          (divisorSeq s.K (fun i => (stages s (i + 1)).K) m)
          (divisorSeq s.B (fun i => (stages s (i + 1)).B) m) c.R c.sT c.g := by
  cases m with
  | zero => exact (stages s 0).trichotomy
  | succ j => exact (stages s (j + 1)).trichotomy

private theorem program_isMaximal (s : Stage) : (program s).IsMaximal := by
  classical
  by_cases h : ∃ i, ¬ (stages s i).HasStep
  · have hn : pN s = (Nat.find h : ℕ∞) := by unfold pN; rw [dif_pos h]
    have hntop : pN s ≠ ⊤ := by rw [hn]; exact ENat.coe_ne_top _
    have hm : (pN s).toNat = Nat.find h := by rw [hn]; rfl
    right
    have key := trichotomy_modelSeq s (Nat.find h)
    rw [← hm] at key
    rcases key with hnef | hstep | hfin
    · exact Or.inl ⟨hntop, hnef⟩
    · exact absurd (hm ▸ hstep) (Nat.find_spec h)
    · exact Or.inr ⟨hntop, hfin⟩
  · left
    change pN s = ⊤
    unfold pN
    rw [dif_neg h]

end Proof_exists_program_isMaximal

namespace MMP.Fourfold

open MMP.Mori

/-- **Existence of maximal programs.** A projective lc fourfold pair `(X, B)` over `ℂ`, with
canonical divisor `K`, has a maximal program. -/
theorem exists_program_isMaximal {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : QDivisor X} (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX B) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) :
    ∃ P : Program sX K B, P.IsMaximal :=
  ⟨Proof_exists_program_isMaximal.program ⟨X, sX, K, B, hX, hlc, hK, hdim⟩,
    Proof_exists_program_isMaximal.program_isMaximal _⟩

end MMP.Fourfold