module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialContractionKlt
import MMP.AlgebraicGeometry.MMP.Threefold.LogMMP
import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModelGraphDivisor
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Intersection.Surface.NegativityLemma
import MMP.AlgebraicGeometry.Divisor.OrderPullback
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.LogResolution.FloorPushforward
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# A crepant floor-lowering program for semiample dlt surfaces

Let `(S, B)` be a `ℚ`-factorial projective dlt complex surface with reduced floor `C = ⌊B⌋`,
and suppose `D = K_S + B` is semiample: `D ∼_ℚ p^*A` for a contraction `p : S ⟶ Y` onto a
normal projective variety and an ample `ℚ`-divisor `A` on `Y`. If `dim Y ≤ 1`, then for every
rational `0 < ε < 1` there is a finite projective program over `Y` for the klt pair
`(S, B - εC)`, all of whose steps are divisorial contractions, crepant for the unlowered
boundaries. Every model `(S_i, B_i)` (with `B_i` the birational transform of `B`) is
`ℚ`-factorial and lc, its lowered boundary is `B_i - ε⌊B_i⌋` and is klt, and each step
`S_i ⟶ S_{i+1}` restricts to a morphism of reduced floors `⌊B_i⌋ ⟶ ⌊B_{i+1}⌋` with
`𝒪_{⌊B_{i+1}⌋} = h_* 𝒪_{⌊B_i⌋}` and connected fibres. The endpoint is nef over `Y` or a Mori
fibre space over `Y`; it is a Mori fibre space when `C` has a component dominating `Y`, or when
`Y` is a point and `C ≠ 0`. When `Y` is a curve and `C` is vertical, the endpoint is nef and its
floor is a union of whole fibres over `Y`.

## Main results

* `MMP.Fourfold.IsContraction.exists_relativeDltProgram_sub_smul_roundDown`.

## Implementation notes

The program is a `MMP.Fourfold.RelativeDltProgram` over `Y` for the lowered boundary
`B - ε⌊B⌋`; since its models are klt, they are in particular `ℚ`-factorial dlt. Semiampleness
of `D` is expressed through its semiample contraction: `p` is a contraction
(`MMP.Fourfold.IsContraction`, so `p_* 𝒪_S = 𝒪_Y` and `Y` is a normal projective variety) and
`D ∼_ℚ p^*A` with `A` ample. A divisorial step is the first alternative of
`MMP.Fourfold.IsElementaryDltStep`: `f_i` is birational with exceptional set a prime divisor and
`f_i⁺` is an isomorphism, so that `q_i : S_i ⟶ S_{i+1}` with `q_i ≫ f_i⁺ = f_i` is the
contraction. Crepancy is `MMP.Mori.IsCrepantBoundary`: `B_i` is the crepant boundary of
`(S_{i+1}, B_{i+1})` on `S_i`. The reduced floors are reduced closed subschemes with support
`⌊B_i⌋`; `q_i` maps the floor of `S_i` into that of `S_{i+1}`, so a morphism `h` of floors
over `q_i` exists, and it is unique since `ι'` is a monomorphism. Dlt of the unlowered
models is not asserted, only lc.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], 3.31
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_lem_mmp_surface_semiample_floor_lowering_program

open MMP.Fourfold MMP.Mori MMP.Flips

/-- The iterated birational transforms `D₀ = D`, `D_{i+1} = (φ_i)_* D_i` of a divisor along a
sequence of rational maps `φ_i : X_i ⤏ X_{i+1}`. -/
private noncomputable def iterTransform {R : Type*} [AddCommMonoid R] {X : Scheme.{0}}
    {Y : ℕ → Scheme.{0}} (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i))
    (D : DivisorWithCoeffs R X) : ∀ i, DivisorWithCoeffs R (modelSeq X Y i)
  | 0 => D
  | i + 1 => MMP.Mori.RationalMap.transformDivisor (φ i) (iterTransform φ D i)

private theorem divisorSeq_iterTransform {R : Type*} [AddCommMonoid R] {X : Scheme.{0}}
    {Y : ℕ → Scheme.{0}} (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i))
    (D : DivisorWithCoeffs R X) :
    ∀ i, divisorSeq D (fun j => iterTransform φ D (j + 1)) i = iterTransform φ D i
  | 0 => rfl
  | _ + 1 => rfl

/-- The invariant carried along the program: on the model `(X, B_X)` over `Y` (by `π`), with
lowered boundary `L`, `L = B_X - ε⌊B_X⌋`, `(X, B_X)` is lc, `X` is a surface,
`K_X + B_X ∼_ℚ π^*A`, and the floor keeps the nonvanishing and verticality of the original
floor. -/
private structure ModelInv {Y X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) (π : X ⟶ Y) {A : QDivisor Y} (hAq : A.IsQCartier) (ε : ℚ)
    (KX : Divisor X) (BX L : QDivisor X) (c0ne c0vert : Prop) : Prop where
  lowered : L = BX - ε • Divisor.toQDivisor BX.roundDown
  lc : MMP.Intersection.IsLogCanonicalPair sX BX
  dim : topologicalKrullDim X = 2
  adj : ∃ hη : ∀ Z : irreducibleComponents X, π (componentGenericPoint X Z) ∉ A.supp,
    (Divisor.toQDivisor KX + BX).QLinearlyEquivalent (A.pullback hAq hη)
  ne : c0ne → BX.roundDown ≠ 0
  dom : IsDominant π
  vert : c0vert → QDivisor.IsVertical π (Divisor.toQDivisor BX.roundDown)
  horiz : ¬ c0vert → ¬ QDivisor.IsVertical π (Divisor.toQDivisor BX.roundDown)

/-- The floor of a coefficient in `[0, 1]` is `1` at `1` and `0` below. -/
private theorem floor_eq_ite {a : ℚ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    (⌊a⌋ : ℚ) = if a = 1 then 1 else 0 := by
  split_ifs with h
  · simp [h]
  · rw [Int.floor_eq_zero_iff.mpr ⟨h0, lt_of_le_of_ne h1 h⟩]
    simp

/-- Lowering the reduced part of a dlt boundary by `0 < ε ≤ 1` gives a dlt boundary. -/
private theorem isDltPair_sub_smul_roundDown {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sX)
    {B : QDivisor X} (hB : MMP.Intersection.IsDltPair sX B) {t : ℚ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) :
    MMP.Intersection.IsDltPair sX (B - t • Divisor.toQDivisor B.roundDown) := by
  have hcoeff : ∀ P, (B - t • Divisor.toQDivisor B.roundDown).coeff P =
      B.coeff P - t * ⌊B.coeff P⌋ := by
    intro P
    simp
  have h0 : ∀ P, 0 ≤ B.coeff P := hB.1.2.1
  have h1 : ∀ P, B.coeff P ≤ 1 := hB.2.1
  have hfl := fun P => floor_eq_ite (h0 P) (h1 P)
  refine MMP.Intersection.IsDltPair.of_le sX hB (fun P => ?_) (fun P => ?_)
    (isQCartier_of_isQFactorial sX hQ _)
  · change (0 : ℚ) ≤ (B - t • Divisor.toQDivisor B.roundDown).coeff P
    rw [hcoeff, hfl]
    split_ifs with h
    · rw [h]; linarith
    · simpa using h0 P
  · change (B - t • Divisor.toQDivisor B.roundDown).coeff P ≤ B.coeff P
    rw [hcoeff, hfl]
    split_ifs <;> simp; linarith

/-- On a log canonical pair every coefficient of the boundary is at most one: the log
discrepancy of a prime divisor `P` is `1 - coeff_P`. -/
private theorem coeff_le_one_of_isLogCanonicalPair {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : B.coeff P ≤ 1 := by
  obtain ⟨⟨hX, n, K, hK, hQ⟩, -, hlc⟩ := hB
  obtain ⟨m, hm, hmC⟩ := hQ.exists_pos
  obtain ⟨-, V, hV, τ, hτ⟩ :=
    MMP.Positivity.IsPair.exists_generatesOn ⟨hX, n, K, hK, hQ⟩ hK hmC P.genericPoint
  have hd : IsDiscrepancy sX n K B (DivisorOver.ofPrimeDivisor k hX P) (-B.coeff P) := by
    refine ⟨hX, hK, m, hm, hmC, V, hV, τ, hτ, ?_⟩
    rw [DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P τ]
    have hPV : (P.support ∩ (V : Set X)).Nonempty := by
      refine ⟨P.genericPoint, ?_, hV⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    linear_combination -hτ.2 P hPV
  have h0 := hlc n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hd
    (show IsProper (𝟙 X) from inferInstance))
  have h1 : ((B.coeff P : ℚ) : ℝ) ≤ 1 := by push_cast at h0; linarith
  exact_mod_cast h1

section Curves

universe u

open Order

variable {k : Type u} [Field k] {S : Scheme.{u}}

/-- The coheight of a point is at most the dimension of the scheme. -/
private theorem coheight_le_of_topologicalKrullDim_le {n : ℕ∞}
    (h : topologicalKrullDim S ≤ n) (x : S) : coheight x ≤ n := by
  have h2 : ringKrullDim (S.presheaf.stalk x) ≤ topologicalKrullDim S := by
    rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk S]
    exact le_iSup (fun y : S => ringKrullDim (S.presheaf.stalk y)) x
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at h2
  exact_mod_cast h2.trans h

/-- A proper curve over `k` is a curve over `k`. -/
private theorem isCurve_properCurve {sS : S ⟶ Spec (.of k)} (C : ProperCurve sS) :
    AlgebraicGeometry.IsCurve k (C.ι ≫ sS) where
  toIsIntegral := inferInstance
  toIsSeparated := inferInstance
  toLocallyOfFiniteType := (inferInstance : IsProper (C.ι ≫ sS)).toLocallyOfFiniteType
  toQuasiCompact := inferInstance
  topologicalKrullDim_eq_one := C.dim_eq

/-- The underlying set of a proper curve is the closure of its generic point. -/
private theorem range_properCurve_ι {sS : S ⟶ Spec (.of k)} (C : ProperCurve sS) :
    Set.range C.ι = closure ({C.point} : Set S) := by
  unfold ProperCurve.ι curveSubschemeAtι
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- A proper curve has more than one point. -/
private theorem not_subsingleton_properCurve {sS : S ⟶ Spec (.of k)} (C : ProperCurve sS) :
    ¬ Subsingleton C.scheme := fun _ => by
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- The generic point of a proper curve is not a closed point. -/
private theorem not_isClosed_point {sS : S ⟶ Spec (.of k)} (C : ProperCurve sS) :
    ¬ IsClosed ({C.point} : Set S) := fun hcl => by
  refine not_subsingleton_properCurve C ⟨fun a b => C.ι.isClosedEmbedding.injective ?_⟩
  have ha : C.ι a ∈ Set.range C.ι := ⟨a, rfl⟩
  have hb : C.ι b ∈ Set.range C.ι := ⟨b, rfl⟩
  rw [range_properCurve_ι, hcl.closure_eq] at ha hb
  exact ha.trans hb.symm

variable (f : S ⟶ Spec (.of k))

/-- The dimension of the reduced closed subscheme on `{x}⁻` is the height of `x`. -/
private theorem topologicalKrullDim_curveSubschemeAt (x : S) :
    topologicalKrullDim (curveSubschemeAt x) = (height x : WithBot ℕ∞) := by
  have h := MMP.Intersection.subvarietyDim_eq_height (MMP.Intersection.associatedSubvariety x)
  rw [MMP.Intersection.genericPoint_associatedSubvariety] at h
  exact h

/-- On an integral `k`-surface locally of finite type, `height x + coheight x = 2`. -/
private theorem height_add_coheight_eq_two [IsIntegral S] [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim S = 2) (x : S) : height x + coheight x = 2 := by
  letI : S.Over (Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType (S ↘ Spec (.of k)) := ‹LocallyOfFiniteType f›
  have hpure : MMP.Intersection.IsPureDimensional S 2 := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ S).isHomeomorph.topologicalKrullDim_eq, hdim]
    rfl
  exact MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure x

private theorem eq_one_of_add_eq_two {a b : ℕ∞} (h : a + b = 2) (hb : b = 1) : a = 1 := by
  subst hb
  exact WithTop.add_right_cancel ENat.one_ne_top (h.trans one_add_one_eq_two.symm)

/-- The generic point of a proper curve on a surface has coheight one. -/
private theorem coheight_point_eq_one [IsIntegral S] [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim S = 2) (C : ProperCurve f) : coheight C.point = 1 := by
  have h := height_add_coheight_eq_two f hdim C.point
  have h1 : height C.point = 1 := by
    have := C.dim_eq
    rw [topologicalKrullDim_curveSubschemeAt] at this
    exact_mod_cast this
  rw [add_comm] at h
  exact eq_one_of_add_eq_two h h1

/-- The generic point of a prime divisor on a proper surface is the generic point of a proper
curve. -/
private theorem isProperCurve_genericPoint [IsProper f] [IsIntegral S]
    (hdim : topologicalKrullDim S = 2) (P : MMP.Mori.PrimeDivisor S) :
    IsProperCurve f P.genericPoint := by
  refine isProperCurve_of_isProper f ?_
  rw [topologicalKrullDim_curveSubschemeAt]
  have h := height_add_coheight_eq_two f hdim P.genericPoint
  rw [eq_one_of_add_eq_two h (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)]
  rfl

end Curves

/-- An open subset on which `f` restricts to an open immersion is one on which `f` is
injective. -/
private theorem injOn_of_isOpenImmersion {X Z : Scheme.{0}} (f : X ⟶ Z) (U : X.Opens)
    [IsOpenImmersion (U.ι ≫ f)] : Set.InjOn f.base (U : Set X) := fun a ha b hb hab =>
  congrArg Subtype.val ((U.ι ≫ f).isOpenEmbedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)

/-- A morphism of schemes over `ℂ` which is injective on an open set `U` containing the generic
point of a proper curve does not contract the curve: `{η} = closure {η} ∩ U` would be locally
closed, hence closed (Jacobson), and the curve would be a point. -/
private theorem not_isContractedBy_of_injOn_of_mem {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] (f : X ⟶ Z) (U : X.Opens)
    (hinj : Set.InjOn f.base (U : Set X)) (C : ProperCurve sX) (hη : C.point ∈ U) :
    ¬ C.IsContractedBy f := by
  intro hC
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hset : ({C.point} : Set X) = closure {C.point} ∩ (U : Set X) := by
    ext x
    refine ⟨fun hx => ?_, fun ⟨hx1, hx2⟩ => hinj hx2 hη (hC x hx1)⟩
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨subset_closure rfl, hη⟩
  have hlc : IsLocallyClosed ({C.point} : Set X) := by
    rw [hset]
    exact (isClosed_closure.isLocallyClosed).inter (U.isOpen.isLocallyClosed)
  exact not_isClosed_point C (isClosed_singleton_of_isLocallyClosed_singleton hlc)

/-- On a surface over `ℂ`, a morphism which is injective off a closed subset of codimension at
least two contracts no proper curve. -/
private theorem not_isContractedBy_of_injOn {X Z : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] (hdim : topologicalKrullDim X = 2)
    (f : X ⟶ Z) (V : Closeds X) (hV : 2 ≤ MMP.Mori.closedsCodimension V)
    (hinj : Set.InjOn f.base ((V.compl : Opens X) : Set X)) (C : ProperCurve sX) :
    ¬ C.IsContractedBy f := by
  by_cases hη : C.point ∈ ((V.compl : Opens X) : Set X)
  · exact not_isContractedBy_of_injOn_of_mem f _ hinj C hη
  · have hηV : C.point ∈ (V : Set X) := by
      simpa [Closeds.compl] using hη
    have h2 := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV) _ hηV
    rw [coheight_point_eq_one sX hdim C] at h2
    exact absurd h2 (by decide)

/-- A small contraction of a surface is never a negative extremal contraction: it contracts no
curve, so `ρ(X/Z) = 0`. -/
private theorem false_of_isSmall_of_isNegativeExtremalContraction {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {E : RDivisor X}
    (hdim : topologicalKrullDim X = 2) (hs : IsSmall ℂ sZ sX f)
    (hc : IsNegativeExtremalContraction ℂ sX sZ E f) : False := by
  obtain ⟨-, V, W, hV, hW, hle, hiso⟩ := hs
  haveI : LocallyOfFiniteType sX := hc.isNormalVariety_source.1.toLocallyOfFiniteType
  have hopen : IsOpenImmersion (Scheme.Opens.ι (X := X) V.compl ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f hle]; infer_instance
  have hinj := injOn_of_isOpenImmersion f V.compl
  have htop : relativeNumericallyTrivialDivisors sX f = ⊤ := by
    rw [eq_top_iff]
    intro D _
    rw [mem_relativeNumericallyTrivialDivisors]
    intro C hC
    exact absurd hC (not_isContractedBy_of_injOn hdim f V hV hinj C)
  have h1 := hc.relativePicardNumber_eq_one
  have h0 : Module.rank ℝ (MMP.Flips.RelativeNumericalDivisorClasses sX f) = 0 := by
    haveI : Subsingleton (MMP.Flips.RelativeNumericalDivisorClasses sX f) :=
      Submodule.Quotient.subsingleton_iff.mpr htop
    exact rank_subsingleton' _ _
  rw [MMP.Flips.relativePicardNumber, h0] at h1
  simp at h1

private theorem compHom_compHom {X Y Z W : Scheme.{0}} (f : X.RationalMap Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) : (f.compHom g).compHom h = f.compHom (g ≫ h) := by
  induction f using Quotient.inductionOn
  rfl

private theorem compHom_id {X Y : Scheme.{0}} (f : X.RationalMap Y) : f.compHom (𝟙 Y) = f := by
  induction f using Quotient.inductionOn with
  | h f =>
    change (f.compHom (𝟙 Y)).toRationalMap = f.toRationalMap
    congr 1

private theorem toRationalMap_compHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rfl

/-- A rational map `φ` over `Z` into the isomorphic `fp : X' ⟶ Z` is the morphism `f ≫ fp⁻¹`. -/
private theorem eq_toRationalMap_of_isOver {X X' Z : Scheme.{0}} (φ : X.RationalMap X')
    (f : X ⟶ Z) (fp : X' ⟶ Z) [IsIso fp] (h : φ.compHom fp = f.toRationalMap) :
    φ = (f ≫ inv fp).toRationalMap := by
  rw [← toRationalMap_compHom, ← h, compHom_compHom, IsIso.hom_inv_id, compHom_id]

/-! ### Log discrepancies along crepant morphisms -/

section LcDescent

universe u

open scoped WithZero

section DiscrepancyChoices

open TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- A discrepancy computed with a form whose divisor is canonical gives the log discrepancy
`1 + a`. -/
private theorem isLogDiscrepancy_of_isDiscrepancyWith {n : ℕ} {D : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {b : ℝ} (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : IsDiscrepancyWith sX n D ω r L E b) :
    MMP.Intersection.IsLogDiscrepancy sX n D E.toDivisorOver (1 + b) := by
  obtain ⟨hX, hn, hω, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω, ⟨divisorOfForm ω, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r,
    L, L', hLc, fun Γ => ?_, hpb, by ring⟩
  have := congrArg (fun D : RDivisor X => D.coeff Γ) hsum
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    MMP.Fourfold.coeff_sum_smul_toRDivisor] using this

/-- With a presentation of `div(ω) + D` by Cartier divisors, every divisor over `X` (with proper
model) has a discrepancy computed with these choices. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {D : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : ProperDivisorOver k sX) : ∃ b, IsDiscrepancyWith sX n D ω r L E b := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨_, hX, hn, hω, hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- The valuation of a divisor over `X` with proper model has nonempty center. -/
private theorem hasNonemptyCenter_valuation (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

end DiscrepancyChoices

section Lift

variable {k : Type u} [Field k] {M W : Scheme.{u}} [IsIntegral M] [IsIntegral W]
  {sM : M ⟶ Spec (.of k)}

/-- **The centre on a proper model.** If `q : W ⟶ M` is proper and dominant and `ξ` is a
valuation of `k(W)` restricting to the valuation of a divisor `D` over `M`, then `ξ` dominates the
local ring of some point of `W` (valuative criterion of properness). -/
private theorem exists_dominated_point (q : W ⟶ M) [IsDominant q] [IsProper q]
    (D : DivisorOver k sM) (ξ : Valuation W.functionField ℤᵐ⁰)
    (h : ξ.comap (functionFieldMap q) = D.valuation) :
    ∃ x : W, (∀ a : W.presheaf.stalk x, ξ (algebraMap _ W.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk x),
        ξ (algebraMap _ W.functionField a) < 1 := by
  set z := D.f D.E.genericPoint
  have hw : ∀ b : M.presheaf.stalk z,
      ξ (functionFieldMap q (algebraMap _ M.functionField b)) =
        D.valuation (algebraMap _ M.functionField b) := fun b => by
    rw [← h]; rfl
  let R := ξ.valuationSubring
  let φ : M.presheaf.stalk z →+* R :=
    ((functionFieldMap q).comp (algebraMap (M.presheaf.stalk z) M.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D z rfl _)
  have hgen : genericPoint M ⤳ z := (genericPoint_spec M).specializes trivial
  have hex : ValuativeCriterion.Existence q := by
    have h : @IsProper _ _ q := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq q :=
    { R := R
      K := W.functionField
      i₁ := W.fromSpecStalk (genericPoint W)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ M.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk q,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R W.functionField)) ≫ l =
      W.fromSpecStalk (genericPoint W) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint W ⤳ x := (genericPoint_spec W).specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R W.functionField) =
      W.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (W.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : W.presheaf.stalk x,
      algebraMap _ W.functionField a = ((f.hom a : R) : W.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]; exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

variable [IsLocallyNoetherian M] [IsNormal M] [IsLocallyNoetherian W] [IsNormal W]

/-- **Lifting a divisor over `M` along a proper birational morphism.** Every divisor `D` over `M`
with proper model has the valuation `ord_E ∘ q^*` of a divisor `E` over `W`, for `q : W ⟶ M`
proper birational with `W` a variety. -/
private theorem exists_properDivisorOver_comap_eq (q : W ⟶ M) [IsProper q]
    (hq : IsBirationalMorphism q) [AlgebraicGeometry.IsVariety k (q ≫ sM)]
    (D : ProperDivisorOver k sM) :
    haveI := hq.isDominant
    ∃ E : ProperDivisorOver k (q ≫ sM),
      E.valuation.comap (functionFieldMap q) = D.valuation := by
  have := hq.isDominant
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have hbq := hq.functionFieldMap_bijective
  let eq := RingEquiv.ofBijective (functionFieldMap q) hbq
  let ξ : Valuation W.functionField ℤᵐ⁰ := D.valuation.comap eq.symm.toRingHom
  have hξ : ξ.comap (functionFieldMap q) = D.valuation := by
    ext a
    change D.valuation (eq.symm (functionFieldMap q a)) = D.valuation a
    rw [show functionFieldMap q a = eq a from rfl, RingEquiv.symm_apply_apply]
  obtain ⟨x, hle, hlt⟩ := exists_dominated_point q D.toDivisorOver ξ hξ
  have hdiv : IsDivisorOfFunctionField k (q ≫ sM) ξ := by
    refine ⟨D.Y, D.f ≫ sM, D.isNormalVariety, D.E, ?_⟩
    letI := functionFieldAlgebra sM
    letI := functionFieldAlgebra (q ≫ sM)
    letI := functionFieldAlgebra (D.f ≫ sM)
    let eP := functionFieldAlgEquiv sM q hbq
    let eY := functionFieldAlgEquiv sM D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbq.2 t
    change D.valuation (eq.symm (functionFieldMap q s)) =
      D.E.divisorialValuation (eY (eP.symm (functionFieldMap q s)))
    have h1 : eP.symm (functionFieldMap q s) = s := eP.symm_apply_apply s
    rw [h1, show functionFieldMap q s = eq s from rfl, RingEquiv.symm_apply_apply]
    rfl
  obtain ⟨E, -, hv, -⟩ := MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (q ≫ sM) hdiv x hle hlt
  exact ⟨E, by rw [hv, hξ]⟩

end Lift

/-! ### Compatible forms -/

section Forms

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

open MMP.Positivity in
/-- For a proper birational morphism `f : Y → X` of normal varieties of dimension `n` and a
canonical divisor `K_Y` of `Y`, there is a nonzero rational top form `ω` on `X` with
`div_Y(f^*ω) = K_Y` and `div_X(ω) = f_* K_Y`. -/
private theorem exists_divisorOfForm_eq_transformDivisor (hX : IsNormalVariety k sX) {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX)) [IsProper f]
    (hf : IsBirationalMorphism f) [IsDominant f] {n : ℕ} (hn : topologicalKrullDim X = n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧
      divisorOfForm ω = RationalMap.transformDivisor (X := Y) f.toRationalMap KY ∧
      divisorOfForm (pullbackRationalPluriForms sX f ω) = KY := by
  have hbij := hf.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨ω₁, hω₁0, hω₁⟩ := IsCanonicalDivisor.exists_ordForm_eq hY hKY
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω₁ ())
  let τ : RationalPluriForms sX n 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sX f τ = ω₁ := by
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 τ = ω₁
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp only [τ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap f g • _ = ω₁
    rw [hg]
    exact basis_unit_repr_smul _ ω₁
  refine ⟨τ, fun h0 => hω₁0 ?_, Finsupp.ext fun P => ?_, Finsupp.ext fun Γ => ?_⟩
  · rw [← hpull, h0]
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 0 = 0
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp
  · obtain ⟨E, heq, hiso, htr⟩ := exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hf P
    rw [htr]
    change P.ordForm τ = KY.coeff E
    rw [← ordForm_pullbackRationalPluriForms_of_isIso f hbij hd E P heq τ, hpull, hω₁]
  · change Γ.ordForm _ = KY.coeff Γ
    rw [hpull, hω₁]

end Forms

/-! ### Log discrepancies along a crepant morphism -/

section CrepantDescent

variable {k : Type u} [Field k] [PerfectField k] {V M : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [LocallyOfFiniteType sV]
  [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M]

/-- **Log discrepancies descend along a crepant proper birational morphism.** Let `q : M ⟶ V` be
proper birational, `ω` a nonzero rational top form on `V` with `K_V = div(ω)` and
`K_M = div(q^*ω)`, and `K_V + B_V` an `ℝ`-Cartier combination whose pull-back is `K_M + B_M`.
If every log discrepancy of `(M, B_M)` is nonnegative, so is every log discrepancy of
`(V, B_V)`: each is the log discrepancy of `(M, B_M)` along the same valuation. -/
private theorem nonneg_of_isLogDiscrepancy_of_isRCartierPullback (hV : IsNormalVariety k sV)
    (q : M ⟶ V) [IsProper q] [IsDominant q] [LocallyOfFiniteType (q ≫ sV)]
    (hM : IsNormalVariety k (q ≫ sV)) (hq : IsBirationalMorphism q) {n : ℕ}
    {ω : RationalPluriForms sV n 1} (hω : ω ≠ 0) (hKV : (divisorOfForm ω).IsCanonicalDivisor sV n)
    (hKM : (divisorOfForm (pullbackRationalPluriForms sV q ω)).IsCanonicalDivisor (q ≫ sV) n)
    {BV : RDivisor V} {BM : RDivisor M} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor V}
    (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + BV = ∑ j, r j • Divisor.toRDivisor (L j))
    (hDY : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ω) + BV)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sV q ω)) + BM))
    (hlc : ∀ (E : DivisorOver k (q ≫ sV)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (q ≫ sV) n BM E a → 0 ≤ a)
    {E : DivisorOver k sV} {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sV n BV E a) :
    0 ≤ a := by
  have := hM.1
  let EP : ProperDivisorOver k sV := ⟨E, ha.2.1⟩
  obtain ⟨b, hb⟩ := exists_isDiscrepancyWith hV hKV.topologicalKrullDim_eq hω hLc hsum EP
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha
    (isLogDiscrepancy_of_isDiscrepancyWith hKV hb)]
  obtain ⟨E', hE'⟩ := exists_properDivisorOver_comap_eq q hq EP
  have hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + BV) :=
    ⟨m, r, L, hLc, by rw [hsum]; simp only [toRDivisor_eq_mapCoeffs]⟩
  obtain ⟨-, -, -, E₀, _, _, _, _, -, hdiv₀, hw₀⟩ :=
    (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hV hω hKV hKD q hM hq hDY hKM E' b).mp
      (hE' ▸ ⟨hKV, hKD, hasNonemptyCenter_valuation EP, EP, ω, m, r, L, rfl, rfl, hb⟩)
  exact hlc E₀.toDivisorOver _ (isLogDiscrepancy_of_isDiscrepancyWith (hdiv₀ ▸ hKM) hw₀)

end CrepantDescent

end LcDescent

/-! ### Push-forward and pull-back along a proper birational morphism -/

section Birational

variable {X X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX' : X' ⟶ Spec (.of ℂ)}

/-- The push-forward of a divisor regarded as a `ℚ`-divisor. -/
private theorem transformDivisor_toQDivisor (hX' : IsNormalVariety ℂ sX') (q : X ⟶ X')
    [IsProper q] (hX : IsNormalVariety ℂ (q ≫ sX')) (hqb : IsBirationalMorphism q)
    (D : Divisor X) :
    RationalMap.transformDivisor (X := X) q.toRationalMap (Divisor.toQDivisor D) =
      Divisor.toQDivisor (RationalMap.transformDivisor (X := X) q.toRationalMap D) := by
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, -, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX' hX hqb P
  rw [htr]
  change (Divisor.toQDivisor D).coeff E =
    (Divisor.toQDivisor (RationalMap.transformDivisor (X := X) q.toRationalMap D)).coeff P
  rw [Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor]
  exact congrArg (fun z : ℤ => (z : ℚ)) (htr D).symm

/-- The push-forward of a principal divisor along a proper birational morphism is principal. -/
private theorem exists_transformDivisor_principalDivisor (hX' : IsNormalVariety ℂ sX')
    (q : X ⟶ X') [IsProper q] (hX : IsNormalVariety ℂ (q ≫ sX')) (hqb : IsBirationalMorphism q)
    (φ : (RationalFunctions X)ˣ) :
    ∃ ψ : (RationalFunctions X')ˣ,
      RationalMap.transformDivisor (X := X) q.toRationalMap (principalDivisor φ) =
        principalDivisor ψ := by
  obtain ⟨ψ, hψ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hqb φ
  exact ⟨ψ, MMP.Positivity.transformDivisor_principalDivisor_pullback hX' hX hqb ψ hψ⟩

/-- Push-forward along a proper birational morphism preserves `ℚ`-linear equivalence. -/
private theorem QLinearlyEquivalent.transformDivisor (hX' : IsNormalVariety ℂ sX')
    (q : X ⟶ X') [IsProper q] (hX : IsNormalVariety ℂ (q ≫ sX')) (hqb : IsBirationalMorphism q)
    {D₁ D₂ : QDivisor X} (h : D₁.QLinearlyEquivalent D₂) :
    QDivisor.QLinearlyEquivalent (RationalMap.transformDivisor (X := X) q.toRationalMap D₁)
      (RationalMap.transformDivisor (X := X) q.toRationalMap D₂) := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := exists_transformDivisor_principalDivisor hX' q hX hqb φ
  refine ⟨m, hm, ψ, ?_⟩
  rw [← map_sub, ← map_zsmul, hφ, transformDivisor_toQDivisor hX' q hX hqb, hψ]

/-- A `ℚ`-divisor which is `ℚ`-linearly trivial and has zero push-forward along a proper
birational morphism is zero. -/
private theorem eq_zero_of_transformDivisor_eq_zero (hX' : IsNormalVariety ℂ sX')
    (q : X ⟶ X') [IsProper q] (hX : IsNormalVariety ℂ (q ≫ sX')) (hqb : IsBirationalMorphism q)
    {H : QDivisor X} (hH : RationalMap.transformDivisor (X := X) q.toRationalMap H = 0)
    (hlin : H.QLinearlyEquivalent 0) : H = 0 := by
  obtain ⟨m, hm, φ, hφ⟩ := hlin
  rw [sub_zero] at hφ
  obtain ⟨ψ, hψ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hqb φ
  have h1 := MMP.Positivity.transformDivisor_principalDivisor_pullback hX' hX hqb ψ hψ
  have h2 : principalDivisor ψ = 0 := by
    apply Divisor.toQDivisor_injective
    rw [← h1, ← transformDivisor_toQDivisor hX' q hX hqb, ← hφ, map_zsmul, hH, smul_zero,
      map_zero]
  have h3 : principalDivisor (pullbackRationalFunction q ψ hψ) = 0 := by
    have hp := Divisor.isPullback_principalDivisor ψ hψ
    haveI := hqb.isDominant
    have h0 := Divisor.isPullback_zero (f := q)
      (fun Z => MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant'
        q _ Z)
    rw [← h2] at h0
    exact hp.eq (Divisor.isCartier_principalDivisor ψ) h0
  rw [h3, map_zero] at hφ
  have hm' : ((m : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  exact (smul_eq_zero.mp hφ).resolve_left hm'

end Birational

/-! ### Pull-backs of `ℚ`-Cartier divisors -/

section Pullbacks

private theorem principalDivisor_zpow {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (φ : (RationalFunctions X)ˣ) (n : ℤ) :
    MMP.Mori.principalDivisor (φ ^ n) = n • MMP.Mori.principalDivisor φ := by
  ext D
  simp [PrimeDivisor.ord_zpow]

/-- Pull-back along a dominant morphism preserves `ℚ`-linear equivalence of `ℚ`-Cartier
`ℚ`-divisors. -/
private theorem QLinearlyEquivalent.of_isPullback {X X' : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] (g : X ⟶ X') [IsDominant g] {N M : QDivisor X'}
    (hNq : N.IsQCartier) (hMq : M.IsQCartier)
    {hBN : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ N.supp}
    {hBM : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ M.supp}
    {NX MX : QDivisor X} (hN : N.IsPullback g hBN NX) (hM : M.IsPullback g hBM MX)
    (h : N.QLinearlyEquivalent M) : NX.QLinearlyEquivalent MX := by
  classical
  obtain ⟨m, hm, φ, hφ⟩ := h
  set a := N.cartierIndex hNq
  set b := M.cartierIndex hMq
  have ha := QDivisor.cartierIndex_pos hNq
  have hb := QDivisor.cartierIndex_pos hMq
  obtain ⟨Da, hDa, hDac⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hNq
  obtain ⟨Db, hDb, hDbc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hMq
  set d : ℕ := a * b * m
  have hd : 0 < d := by positivity
  set DN : Divisor X' := (((b * m : ℕ) : ℤ)) • Da
  set DM : Divisor X' := (((a * m : ℕ) : ℤ)) • Db
  have hDN : Divisor.toQDivisor DN = (d : ℤ) • N := by
    rw [map_zsmul, hDa, smul_smul]
    congr 1
    push_cast [d]
    ring
  have hDM : Divisor.toQDivisor DM = (d : ℤ) • M := by
    rw [map_zsmul, hDb, smul_smul]
    congr 1
    push_cast [d]
    ring
  set ψ := φ ^ (((a * b : ℕ) : ℤ))
  have hDNM : DN = DM + principalDivisor ψ := by
    apply Divisor.toQDivisor_injective
    rw [map_add, hDN, hDM, principalDivisor_zpow, map_zsmul, ← hφ, smul_smul]
    have hdm : ((d : ℕ) : ℤ) = ((a * b : ℕ) : ℤ) * (m : ℤ) := by push_cast [d]; ring
    rw [hdm, smul_sub]
    abel
  have hgen : ∀ (D : Divisor X') (Z : irreducibleComponents X),
      g (componentGenericPoint X Z) ∉ D.supp := fun D Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g D Z
  obtain ⟨DN', hDN', hpN⟩ := hN d hd DN hDN (hDac.zsmul _)
  obtain ⟨DM', hDM', hpM⟩ := hM d hd DM hDM (hDbc.zsmul _)
  have hpψ := Divisor.isPullback_principalDivisor ψ (hgen _)
  have hsum := Divisor.IsPullback.add (hDbc.zsmul _) (Divisor.isCartier_principalDivisor ψ)
    (hgen _) hpM hpψ
  have hpN' := hpN.of_eq hDNM (hB₂ := hgen _)
  have heq := hpN'.eq ((hDbc.zsmul _).add (Divisor.isCartier_principalDivisor ψ)) hsum
  refine ⟨d, hd, pullbackRationalFunction g ψ (hgen _), ?_⟩
  rw [smul_sub, ← hDN', ← hDM', ← map_sub, heq]
  congr 1
  abel

/-- Pull-back of `ℚ`-divisors along a dominant composite. -/
private theorem qDivisor_isPullback_comp
    {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IrreducibleSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (p : Y ⟶ X) (q : Z ⟶ Y) [IsDominant (q ≫ p)]
    {M : QDivisor X} {MY : QDivisor Y} {MZ : QDivisor Z}
    {hM : ∀ C : irreducibleComponents Y, p (componentGenericPoint Y C) ∉ M.supp}
    {hMY : ∀ C : irreducibleComponents Z, q (componentGenericPoint Z C) ∉ MY.supp}
    (h₁ : M.IsPullback p hM MY) (h₂ : MY.IsPullback q hMY MZ) :
    ∃ hM' : ∀ C : irreducibleComponents Z, (q ≫ p) (componentGenericPoint Z C) ∉ M.supp,
      M.IsPullback (q ≫ p) hM' MZ := by
  refine ⟨MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ M,
    fun m hm D hD hDc => ?_⟩
  obtain ⟨D', hD', hpb⟩ := h₁ m hm D hD hDc
  obtain ⟨D'', hD'', hpb'⟩ := h₂ m hm D' hD' (hpb.isCartier hDc)
  exact ⟨D'', hD'', MMP.ProgramBaseChange.divisor_isPullback_comp rfl hpb hpb' _⟩

end Pullbacks

section RIntersection

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : MMP.Flips.IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  refine not_subsingleton_properCurve C ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := ν.surjective a
  obtain ⟨x', rfl⟩ := ν.surjective b
  exact (hy x).trans (hy x').symm

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : MMP.Flips.IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : MMP.Flips.IsCurveNormalization ν)
    (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    degreeOn k sX (ν ≫ C.ι) hdim M = degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  haveI := isCurve_comp C hν hdim
  haveI := isCurve_properCurve C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [degreeOn, degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : MMP.Flips.IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- Every Cartier divisor has an intersection number with a proper curve: the normalization
of the curve is a normal proper curve birational to it. -/
private theorem exists_isCartierIntersectionNumber (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) : ∃ d, MMP.Flips.IsCartierIntersectionNumber k sX C L hL d := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := isCurve_properCurve C
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : MMP.Flips.IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact MMP.Flips.isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV
          hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

/-- A presentation `D = ∑ rⱼ Lⱼ` computes `D · C = ∑ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
private theorem isRIntersectionNumber_sum (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    MMP.Flips.IsRIntersectionNumber k sX D r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) := by
  choose d hd using fun j => exists_isCartierIntersectionNumber C (L j) (hL j)
  refine ⟨hL, d, hD, hd, Finset.sum_congr rfl fun j _ => ?_⟩
  rw [eq_degreeOn (hd j)]

/-- **Real intersection numbers of `ℚ`-Cartier divisors.** For a `ℚ`-Cartier `D`, every value of
the real intersection number of `D` with a proper curve `C` (from any presentation of `D` by
Cartier divisors) is the intersection number `D · C`. -/
private theorem intersectionNumber_eq_of_isRIntersectionNumber {D : QDivisor X}
    (hD : D.IsQCartier) (C : ProperCurve sX) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {x : ℝ} (hx : MMP.Flips.IsRIntersectionNumber k sX (QDivisor.toRDivisor D) r L C x) :
    ((D.intersectionNumber k sX C.ι C.dim_le hD : ℚ) : ℝ) = x := by
  set c := D.cartierIndex hD
  have hc : (0 : ℚ) < c := by exact_mod_cast QDivisor.cartierIndex_pos hD
  set M : Divisor X := (D.cartierIndexSMul hD : Divisor X)
  have hM : M.IsCartier := (D.cartierIndexSMul hD).2
  have hMD := QDivisor.toQDivisor_cartierIndexSMul D hD
  have hDR : QDivisor.toRDivisor D =
      ∑ _j : Fin 1, ((1 : ℝ) / c) • Divisor.toRDivisor M := by
    ext P
    have hP := congrArg (fun E => DivisorWithCoeffs.coeff E P) hMD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at hP
    simp only [QDivisor.coeff_toRDivisor, Finset.univ_unique, Finset.sum_singleton,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    have : ((M.coeff P : ℚ) : ℝ) = (c : ℝ) * (D.coeff P : ℝ) := by
      rw [hP]; push_cast; ring
    rw [show ((M.coeff P : ℤ) : ℝ) = ((M.coeff P : ℚ) : ℝ) by push_cast; rfl, this]
    field_simp
  have hy := isRIntersectionNumber_sum C (fun _ : Fin 1 => (1 : ℝ) / c) (fun _ => M)
    (fun _ => hM) hDR
  have heq := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L _ _ _ _ hx hy
  rw [heq, QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D hD M hM hMD]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  push_cast
  ring

/-- A `ℚ`-Cartier divisor whose real divisor is `f`-nef is nonnegative on `f`-contracted curves. -/
private theorem intersectionNumber_nonneg_of_isRelativelyNef {V : Scheme.{u}}
    (f : X ⟶ V) {D : QDivisor X} (hD : D.IsQCartier)
    (h : MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor D)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : 0 ≤ D.intersectionNumber k sX C.ι C.dim_le hD := by
  obtain ⟨m, r, L, hL, hDeq, hnn⟩ := h
  have hx := isRIntersectionNumber_sum C r L hL hDeq
  have h0 := hnn C hC _ hx
  rw [← intersectionNumber_eq_of_isRIntersectionNumber hD C hx] at h0
  exact_mod_cast h0

/-- A relatively ample Cartier divisor has positive degree on every contracted proper curve. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier' [CompactSpace X] {V : Scheme.{u}}
    {g : X ⟶ V} {L : Divisor X} (hL : MMP.Flips.IsRelativelyAmpleCartier g L)
    (C : ProperCurve sX) (hC : C.IsContractedBy g) :
    0 < L.degreeOn k sX C.ι C.dim_le hL.1 := by
  obtain ⟨hLc, hamp⟩ := hL
  haveI := hLc.isInvertibleModule_divisorialSheaf
  have hM : MMP.Mori.IsRelativelyAmple g L.divisorialSheaf := fun y => by
    obtain ⟨W, hW, hyW, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : V.Opens) from trivial)
    exact ⟨W, hW, hyW, hamp W hW⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy g _ hM C hC

/-- **A `ℚ`-Cartier divisor whose negative is `f`-ample is negative on `f`-contracted curves.** -/
private theorem intersectionNumber_neg_of_isRelativelyAntiAmple [CompactSpace X] {V : Scheme.{u}}
    (f : X ⟶ V) {D : QDivisor X} (hD : D.IsQCartier)
    (hA : MMP.Flips.IsRelativelyAntiAmple f (QDivisor.toRDivisor D)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : D.intersectionNumber k sX C.ι C.dim_le hD < 0 := by
  obtain ⟨m, r, A, hm, hr, hAa, hLeq⟩ := hA
  have hAc : ∀ j, (A j).IsCartier := fun j => (hAa j).1
  have hLeq' : QDivisor.toRDivisor D = ∑ j, (-r j) • Divisor.toRDivisor (A j) := by
    have hL' : QDivisor.toRDivisor D = -(-QDivisor.toRDivisor D) := (neg_neg _).symm
    rw [hL', hLeq]
    simp [neg_smul, Finset.sum_neg_distrib]
  have hx := isRIntersectionNumber_sum C (fun j => -r j) A hAc hLeq'
  have hpos : ∀ j, (0 : ℝ) < (A j).degreeOn k sX C.ι C.dim_le (hAc j) := fun j => by
    exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier' (hAa j) C hC
  have hsum : 0 < ∑ j, r j * ((A j).degreeOn k sX C.ι C.dim_le (hAc j) : ℝ) :=
    Finset.sum_pos (fun j _ => mul_pos (hr j) (hpos j)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have heq := intersectionNumber_eq_of_isRIntersectionNumber hD C hx
  have : ((D.intersectionNumber k sX C.ι C.dim_le hD : ℚ) : ℝ) < 0 := by
    rw [heq]
    simp only [neg_mul, Finset.sum_neg_distrib]
    linarith
  exact_mod_cast this

end RIntersection

/-! ### Intersection numbers with curves -/

section Intersection

/-- Intersection numbers with a proper curve depend only on the `ℚ`-linear equivalence class. -/
private theorem intersectionNumber_eq_of_qLinearlyEquivalent {X C : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    {D₁ D₂ : QDivisor X} (hD₁ : D₁.IsQCartier) (hD₂ : D₂.IsQCartier)
    (h : D₁.QLinearlyEquivalent D₂) :
    D₁.intersectionNumber ℂ sX i hdim hD₁ = D₂.intersectionNumber ℂ sX i hdim hD₂ := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  have ha := QDivisor.cartierIndex_pos hD₂
  obtain ⟨Da, hDa, hDac⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hD₂
  set a := D₂.cartierIndex hD₂
  have hN : 0 < m * a := Nat.mul_pos hm ha
  set ψ := φ ^ (a : ℤ)
  have hE2 : Divisor.toQDivisor ((m : ℤ) • Da) = (((m * a : ℕ)) : ℤ) • D₂ := by
    rw [map_zsmul, hDa, smul_smul]
    push_cast
    ring_nf
  have hE1 : Divisor.toQDivisor ((m : ℤ) • Da + MMP.Mori.principalDivisor ψ) =
      (((m * a : ℕ)) : ℤ) • D₁ := by
    rw [map_add, hE2, principalDivisor_zpow, map_zsmul, ← hφ, smul_smul]
    have : (((m * a : ℕ)) : ℤ) = (a : ℤ) * (m : ℤ) := by push_cast; ring
    rw [this, smul_sub]
    abel
  have hc1 := (hDac.zsmul (m : ℤ)).add (Divisor.isCartier_principalDivisor ψ)
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX i hdim D₁ hD₁ hN _ hc1 hE1,
    QDivisor.intersectionNumber_eq_of_smul ℂ sX i hdim D₂ hD₂ hN _ (hDac.zsmul _) hE2,
    Divisor.degreeOn_add ℂ sX i hdim _ _ (hDac.zsmul _) (Divisor.isCartier_principalDivisor ψ),
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX i hdim
      (Divisor.isCartier_principalDivisor ψ) ⟨ψ, by rw [sub_zero]⟩]
  simp

/-- **A divisor `ℚ`-linearly equivalent to a pull-back from `Y` is numerically trivial over
`Y`**: it has intersection number zero with every proper curve contracted to a point of `Y`. -/
private theorem intersectionNumber_eq_zero_of_isContractedBy {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    (hXv : MMP.Mori.IsVariety ℂ sX) (hYv : MMP.Mori.IsVariety ℂ sY) {π : X ⟶ Y}
    (hπ : π ≫ sY = sX) {A : QDivisor Y} (hAq : A.IsQCartier)
    {hη : ∀ Z : irreducibleComponents X, π (componentGenericPoint X Z) ∉ A.supp}
    {D : QDivisor X} (hD : D.IsQCartier) (hDA : D.QLinearlyEquivalent (A.pullback hAq hη))
    (C : ProperCurve sX) (hC : C.IsContractedBy π) :
    D.intersectionNumber ℂ sX C.ι C.dim_le hD = 0 := by
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI := hXv
  haveI := hYv
  have hpb := QDivisor.isPullback_pullback hAq hη
  have hpbq : (A.pullback hAq hη).IsQCartier := hpb.isQCartier hAq
  rw [intersectionNumber_eq_of_qLinearlyEquivalent C.ι C.dim_le hD hpbq hDA]
  haveI := isCurve_properCurve C
  have hpt : Set.range (C.ι ≫ π).base = {π C.point} := by
    have hr := range_properCurve_ι C
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      have hc : C.ι c ∈ closure ({C.point} : Set X) := hr ▸ ⟨c, rfl⟩
      exact hC _ hc
    · rintro rfl
      obtain ⟨c, hc⟩ : C.point ∈ Set.range C.ι := by rw [hr]; exact subset_closure rfl
      exact ⟨c, by simp [hc]⟩
  exact MMP.Mori.intersectionNumber_pullback_eq_zero ℂ sX sY π hπ C.ι hAq hpb ⟨_, hpt⟩

end Intersection

/-- **On a model of the program the lowered adjoint is `-ε⌊B⌋` over `Y`.** Since
`K + L = (K + B) - ε⌊B⌋` and `K + B ∼_ℚ π^*A`, every proper curve `C` contracted by `π` has
`(K + L)·C = -ε (⌊B⌋·C)`. -/
private theorem ModelInv.intersectionNumber_eq {X Y : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    (hQ : IsQFactorial sX) (hYv : MMP.Mori.IsVariety ℂ sY) {π : X ⟶ Y} (hπ : π ≫ sY = sX)
    {A : QDivisor Y} {hAq : A.IsQCartier} {ε : ℚ} {KX : Divisor X} {BX L : QDivisor X}
    {c0ne c0vert : Prop} (h : ModelInv sX π hAq ε KX BX L c0ne c0vert) (C : ProperCurve sX)
    (hC : C.IsContractedBy π) (hD : (Divisor.toQDivisor KX + L).IsQCartier) :
    (Divisor.toQDivisor KX + L).intersectionNumber ℂ sX C.ι C.dim_le hD =
      -ε * (Divisor.toQDivisor BX.roundDown).intersectionNumber ℂ sX C.ι C.dim_le
        (isQCartier_of_isQFactorial sX hQ _) := by
  obtain ⟨hη, hadj⟩ := h.adj
  have hqf := fun D : QDivisor X => isQCartier_of_isQFactorial sX hQ D
  rw [intersectionNumber_congr (k := ℂ) sX C.ι C.dim_le hD (hqf _)
      (show Divisor.toQDivisor KX + L =
        (Divisor.toQDivisor KX + BX) + (-ε) • Divisor.toQDivisor BX.roundDown by
        rw [h.lowered, neg_smul, ← sub_eq_add_neg, add_sub_assoc]),
    MMP.Mori.QDivisor.intersectionNumber_add' ℂ _ _ _ _ _ (hqf _) (hqf _),
    MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le _ (hqf _) (-ε) (hqf _),
    intersectionNumber_eq_zero_of_isContractedBy hQ.1.1 hYv hπ hAq (hqf _) hadj C hC, zero_add]

/-- On a surface, a canonical divisor is a canonical divisor in dimension two. -/
private theorem isCanonicalDivisor_two {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} (hdim : topologicalKrullDim X = 2)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) : K.IsCanonicalDivisor sX 2 := by
  obtain ⟨m, hm⟩ := hK
  obtain rfl : m = 2 := by exact_mod_cast hm.topologicalKrullDim_eq.symm.trans hdim
  exact hm

/-- **Crepant transfer along a proper birational morphism over `Y`.** Let `q : X ⟶ X'` be a
proper birational morphism of normal varieties with `X'` `ℚ`-factorial, `π' : X' ⟶ Y`, and
`K_X + B_X ∼_ℚ (q ≫ π')^*A`. With `ω` a rational top form on `X'` such that `div(q^*ω) = K_X`,
`div ω + q_*B_X ∼_ℚ π'^*A` and `q^*(div ω + q_*B_X) = K_X + B_X`. -/
private theorem crepant_step {X X' Y : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sX' : X' ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX'] (hX' : IsNormalVariety ℂ sX')
    (hQ' : IsQFactorial sX') (q : X ⟶ X') [IsProper q] [IsDominant q]
    [LocallyOfFiniteType (q ≫ sX')] (hX : IsNormalVariety ℂ (q ≫ sX'))
    (hqb : IsBirationalMorphism q) (π' : X' ⟶ Y) [IsDominant π'] {A : QDivisor Y}
    (hAq : A.IsQCartier)
    (hη : ∀ Z : irreducibleComponents X, (q ≫ π') (componentGenericPoint X Z) ∉ A.supp)
    (hη' : ∀ Z : irreducibleComponents X', π' (componentGenericPoint X' Z) ∉ A.supp)
    {KX : Divisor X} (hKX : KX.IsCanonicalDivisor (q ≫ sX') 2) {BX : QDivisor X}
    (hadj : (Divisor.toQDivisor KX + BX).QLinearlyEquivalent (A.pullback hAq hη)) :
    ∃ ω : RationalPluriForms sX' 2 1, ω ≠ 0 ∧
      divisorOfForm ω = RationalMap.transformDivisor (X := X) q.toRationalMap KX ∧
      divisorOfForm (pullbackRationalPluriForms sX' q ω) = KX ∧
      (Divisor.toQDivisor (divisorOfForm ω) +
        RationalMap.transformDivisor (X := X) q.toRationalMap BX).QLinearlyEquivalent
          (A.pullback hAq hη') ∧
      ∃ hB, (Divisor.toQDivisor (divisorOfForm ω) +
        RationalMap.transformDivisor (X := X) q.toRationalMap BX).IsPullback q hB
          (Divisor.toQDivisor KX + BX) := by
  classical
  haveI := hX'.1
  haveI := hX.1
  have hn : topologicalKrullDim X' = (2 : ℕ) := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' (q ≫ sX') hqb]
    exact hKX.topologicalKrullDim_eq
  obtain ⟨ω, hω0, hωX', hωX⟩ := exists_divisorOfForm_eq_transformDivisor hX' hX hqb hn hKX
  refine ⟨ω, hω0, hωX', hωX, ?_⟩
  set B' := RationalMap.transformDivisor (X := X) q.toRationalMap BX
  set M := A.pullback hAq hη'
  have hgen : ∀ (D : QDivisor X') (Z : irreducibleComponents X),
      q (componentGenericPoint X Z) ∉ D.supp := fun D Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q D Z
  have hMq : M.IsQCartier := isQCartier_of_isQFactorial sX' hQ' M
  have hMX := QDivisor.isPullback_pullback hMq (hgen M)
  set MX := M.pullback hMq (hgen M)
  obtain ⟨hη2, hcomp⟩ := qDivisor_isPullback_comp π' q (QDivisor.isPullback_pullback hAq hη') hMX
  have hMXeq : A.pullback hAq hη = MX := hcomp.pullback_eq hAq
  rw [hMXeq] at hadj
  set N := Divisor.toQDivisor (divisorOfForm ω) + B'
  have hNq : N.IsQCartier := isQCartier_of_isQFactorial sX' hQ' N
  have hNX := QDivisor.isPullback_pullback hNq (hgen N)
  set NX := N.pullback hNq (hgen N)
  have hpushKB : RationalMap.transformDivisor (X := X) q.toRationalMap
      (Divisor.toQDivisor KX + BX) = N := by
    rw [map_add, transformDivisor_toQDivisor hX' q hX hqb, ← hωX']
  have hpushMX : RationalMap.transformDivisor (X := X) q.toRationalMap MX = M :=
    MMP.Positivity.transformDivisor_of_isPullback hX' hX hqb hMq (hgen M) hMX
  have hpushNX : RationalMap.transformDivisor (X := X) q.toRationalMap NX = N :=
    MMP.Positivity.transformDivisor_of_isPullback hX' hX hqb hNq (hgen N) hNX
  have hNM : N.QLinearlyEquivalent M := by
    have := QLinearlyEquivalent.transformDivisor hX' q hX hqb hadj
    rwa [hpushKB, hpushMX] at this
  refine ⟨hNM, hgen N, ?_⟩
  have hNXMX := QLinearlyEquivalent.of_isPullback q hNq hMq hNX hMX hNM
  have hH : NX - (Divisor.toQDivisor KX + BX) = 0 := by
    apply eq_zero_of_transformDivisor_eq_zero hX' q hX hqb
    · rw [map_sub, hpushNX, hpushKB, sub_self]
    · obtain ⟨m, hm, φ, hφ⟩ := hNXMX.trans hadj.symm
      exact ⟨m, hm, φ, by rw [sub_zero]; exact hφ⟩
  rw [← sub_eq_zero.mp hH]
  exact hNX

/-- The crepant boundary does not depend on the choice of canonical divisor. -/
private theorem isCrepantBoundary_of_linearlyEquivalent {X X' : Scheme.{0}} [IsIntegral X']
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] {sX' : X' ⟶ Spec (.of ℂ)} {n : ℕ}
    {K K' : Divisor X'} {Δ : QDivisor X'} {f : X ⟶ X'} {hY : IsNormalVariety ℂ (f ≫ sX')}
    {hf : IsBirationalMorphism f} {ΔY : QDivisor X}
    (h : IsCrepantBoundary sX' n K Δ f hY hf ΔY) (hKK' : K.LinearlyEquivalent K') :
    IsCrepantBoundary sX' n K' Δ f hY hf ΔY := by
  intro F
  obtain ⟨hXv, hK, m, hm, ⟨D, hD, hDc⟩, U, hU, τ, hτ, ha⟩ := h F
  obtain ⟨φ, hφ⟩ := hKK'.symm
  refine ⟨hXv, hK.of_linearlyEquivalent hKK'.symm, m, hm, ⟨D + (m : ℤ) • principalDivisor φ, ?_,
    hDc.add ((Divisor.isCartier_principalDivisor φ).zsmul _)⟩, U, hU, τ, hτ, ha⟩
  rw [map_add, hD, map_zsmul, ← hφ, map_sub, ← smul_add]
  congr 1
  abel

/-- **Log canonicity descends along a crepant proper birational morphism.** -/
private theorem isLogCanonicalPair_of_isPullback {X X' : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX' : X' ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX']
    (hX' : IsNormalVariety ℂ sX') (hQ' : IsQFactorial sX') (q : X ⟶ X') [IsProper q]
    [IsDominant q] [LocallyOfFiniteType (q ≫ sX')] (hX : IsNormalVariety ℂ (q ≫ sX'))
    (hqb : IsBirationalMorphism q) {ω : RationalPluriForms sX' 2 1} (hω : ω ≠ 0)
    (hKV : (divisorOfForm ω).IsCanonicalDivisor sX' 2)
    (hKM : (divisorOfForm (pullbackRationalPluriForms sX' q ω)).IsCanonicalDivisor (q ≫ sX') 2)
    {B' : QDivisor X'} {BX : QDivisor X} (hB' : ∀ P, 0 ≤ B'.coeff P)
    {hB : ∀ Z : irreducibleComponents X, q (componentGenericPoint X Z) ∉
      (Divisor.toQDivisor (divisorOfForm ω) + B').supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm ω) + B').IsPullback q hB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX' q ω)) + BX))
    (hlc : MMP.Intersection.IsLogCanonicalPair (q ≫ sX') BX) :
    MMP.Intersection.IsLogCanonicalPair sX' B' := by
  classical
  set N := Divisor.toQDivisor (divisorOfForm ω) + B'
  have hNq : N.IsQCartier := isQCartier_of_isQFactorial sX' hQ' N
  have hm := QDivisor.cartierIndex_pos hNq
  obtain ⟨D, hD, hDc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hNq
  set m := N.cartierIndex hNq
  obtain ⟨D', hD', hpD⟩ := hpb m hm D hD hDc
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  set r : Fin 1 → ℝ := fun _ => (m : ℝ)⁻¹
  have hcoeff : ∀ {Z : Scheme.{0}} (G : Divisor Z) (K₀ : Divisor Z) (Δ₀ : QDivisor Z)
      (hG : Divisor.toQDivisor G = (m : ℤ) • (Divisor.toQDivisor K₀ + Δ₀)),
      Divisor.toRDivisor K₀ + QDivisor.toRDivisor Δ₀ =
        ∑ j, r j • Divisor.toRDivisor ((fun _ : Fin 1 => G) j) := by
    intro Z G K₀ Δ₀ hG
    refine DivisorWithCoeffs.ext' fun P => ?_
    rw [MMP.Fourfold.coeff_sum_smul_toRDivisor, Fin.sum_univ_one, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor]
    have h1 := congrArg (fun G' : QDivisor Z => G'.coeff P) hG
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      zsmul_eq_mul, Int.cast_natCast] at h1
    have h2 : ((G.coeff P : ℤ) : ℝ) = (m : ℝ) * (((K₀.coeff P : ℤ) : ℝ) + ((Δ₀.coeff P : ℚ) : ℝ)) := by
      have := congrArg (fun t : ℚ => (t : ℝ)) h1
      push_cast at this
      exact this
    simp only [r]
    rw [h2]
    field_simp
  have hsum := hcoeff D (divisorOfForm ω) B' hD
  have hsum' := hcoeff D' (divisorOfForm (pullbackRationalPluriForms sX' q ω)) BX hD'
  have hDY : IsRCartierPullback q
      (Divisor.toRDivisor (divisorOfForm ω) + QDivisor.toRDivisor B')
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX' q ω)) +
        QDivisor.toRDivisor BX) :=
    ⟨1, r, fun _ => D, fun _ => D', fun _ => hDc, hsum, fun _ => ⟨_, hpD⟩, hsum'⟩
  refine ⟨⟨hX', 2, divisorOfForm ω, hKV, hNq⟩, hB', fun n E a ha => ?_⟩
  obtain rfl : n = 2 := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hKV.topologicalKrullDim_eq
  exact nonneg_of_isLogDiscrepancy_of_isRCartierPullback hX' q hX hqb hω hKV hKM
    (fun _ => hDc) hsum hDY (hlc.2.2 _) ha

/-! ### The exceptional divisor of a birational surface contraction -/

section Exceptional

/-- A proper birational morphism `μ : Y ⟶ X` of varieties onto a normal variety is an isomorphism
over a neighbourhood of every point `x` of `X` whose local ring is a valuation ring. -/
private theorem mem_biregularLocus_of_valuationRing {Y X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {μ : Y ⟶ X}
    [IsProper μ] (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ) (x : X)
    [ValuationRing (X.presheaf.stalk x)] : x ∈ biregularLocus μ := by
  have : IsIntegral Y := hY.toIsIntegral
  have : IsNormal X := hX.2
  have : IsDominant μ := hμ.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (μ ≫ sX) := hY.toIsSeparated
  have : IsSeparated μ := IsSeparated.of_comp μ sX
  have hbij := hμ.functionFieldMap_bijective
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso μ
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hμ)).1 inferInstance
  let V : X.Opens := ⟨_, hU⟩
  have hxV : x ∈ V := by
    change (μ ⁻¹' {x}).Finite
    refine Set.Subsingleton.finite fun a ha b hb => ?_
    have ha' : μ a = x := ha
    have hb' : μ b = x := hb
    have : ValuationRing (X.presheaf.stalk (μ a)) := by rw [ha']; infer_instance
    have : ValuationRing (X.presheaf.stalk (μ b)) := by rw [hb']; infer_instance
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij a
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij b
    exact MMP.Positivity.eq_of_isIso_stalkMap μ hbij (hb'.trans ha'.symm)
  exact le_biregularLocus (f := μ) (V := V) hiso hxV

/-- **A birational morphism of surfaces contracts its exceptional curves.** Let `μ : Y ⟶ X` be
a proper birational morphism of varieties onto a normal surface. A point of `Y` whose image lies
outside the biregular locus maps to a point of coheight `2`, so every point of its closure has
the same image. -/
private theorem map_eq_of_mem_closure_of_mem_exceptionalSet {Y X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (hdim : topologicalKrullDim X = 2) {μ : Y ⟶ X} [IsProper μ]
    (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ) {y : Y}
    (hy : y ∈ (MMP.Mori.exceptionalSet μ : Set Y)) {x : Y} (hx : x ∈ closure ({y} : Set Y)) :
    μ x = μ y := by
  have : IsNormal X := hX.2
  have hz : μ y ∉ biregularLocus μ := hy
  -- the coheight of `μ y` is at least two
  have h2 : (2 : ℕ∞) ≤ Order.coheight (μ y) := by
    by_contra hlt
    push Not at hlt
    have hle : Order.coheight (μ y) ≤ 1 := Order.le_of_lt_add_one hlt
    rcases (show Order.coheight (μ y) = 0 ∨ Order.coheight (μ y) = 1 by
      rcases eq_or_lt_of_le hle with h | h
      · exact Or.inr h
      · exact Or.inl (ENat.lt_one_iff_eq_zero.mp h)) with h0 | h1
    · -- `μ y` is the generic point
      have hgen : μ y = genericPoint X := by
        have hmax := Order.coheight_eq_zero.mp h0
        have hsp : genericPoint X ⤳ μ y := (genericPoint_spec X).specializes trivial
        exact (hsp.antisymm (hmax hsp)).eq.symm
      have : ValuationRing (X.presheaf.stalk (μ y)) := by
        rw [hgen]; exact inferInstanceAs (ValuationRing X.functionField)
      exact hz (mem_biregularLocus_of_valuationRing hX hY hμ _)
    · -- `μ y` is the generic point of a prime divisor
      let P : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
      have hP : P.genericPoint = μ y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      have := P.isDiscreteValuationRing_localRing
      have : ValuationRing (X.presheaf.stalk (μ y)) := by
        rw [← hP]; exact inferInstanceAs (ValuationRing P.localRing)
      exact hz (mem_biregularLocus_of_valuationRing hX hY hμ _)
  by_contra hne
  have hsp : μ y ⤳ μ x := (specializes_iff_mem_closure.mpr hx).map μ.base.hom.continuous
  have hlt : μ x < μ y := lt_of_le_not_ge hsp fun h => hne (Specializes.antisymm h hsp).eq
  have h4 := coheight_le_of_topologicalKrullDim_le hdim.le (μ x)
  have h5 := coheight_le_of_topologicalKrullDim_le hdim.le (μ y)
  have h3 := Order.coheight_strictAnti hlt (lt_of_le_of_lt h5 (by decide))
  have : (2 : ℕ∞) < Order.coheight (μ x) := lt_of_le_of_lt h2 h3
  exact absurd (lt_of_lt_of_le this (by exact_mod_cast h4)) (lt_irrefl _)

/-- The support of a prime divisor over which `E` lies is the image of the support of `E`. -/
private theorem support_eq_image_of_map_genericPoint_eq {X X' : Scheme.{0}} (q : X ⟶ X')
    [UniversallyClosed q] {E : MMP.Mori.PrimeDivisor X} {P : MMP.Mori.PrimeDivisor X'}
    (h : q E.genericPoint = P.genericPoint) :
    (P.support : Set X') = q.base '' E.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    ← q.isClosedMap.closure_image_eq_of_continuous q.base.hom.continuous, Set.image_singleton, h]

/-- A point of the source of a proper birational morphism of varieties onto a normal surface
whose image lies over the biregular locus and is the generic point of a prime divisor `E` maps to
the generic point of a prime divisor. -/
private theorem exists_map_genericPoint_eq_of_notMem_exceptionalSet {X X' : Scheme.{0}}
    (q : X ⟶ X') {E : MMP.Mori.PrimeDivisor X}
    (hE : E.genericPoint ∉ (MMP.Mori.exceptionalSet q : Set X)) :
    ∃ P : MMP.Mori.PrimeDivisor X', q E.genericPoint = P.genericPoint := by
  set V := biregularLocus q
  have hV : q E.genericPoint ∈ V := by simpa [MMP.Mori.mem_exceptionalSet] using hE
  have hiso : IsIso (q ∣_ V) := isBiregular_biregularLocus q
  have hopen : IsOpenImmersion ((q ⁻¹ᵁ V).ι ≫ q) := by
    rw [← morphismRestrict_ι]; infer_instance
  have hcoh : Order.coheight (q E.genericPoint) = 1 := by
    have h1 := coheight_eq_of_isOpenImmersion ((q ⁻¹ᵁ V).ι ≫ q)
      (x := (⟨E.genericPoint, hV⟩ : (q ⁻¹ᵁ V).toScheme))
    have h2 := coheight_eq_of_isOpenImmersion (q ⁻¹ᵁ V).ι
      (x := (⟨E.genericPoint, hV⟩ : (q ⁻¹ᵁ V).toScheme))
    change Order.coheight (q E.genericPoint) = _ at h1
    change Order.coheight E.genericPoint = _ at h2
    rw [h1, ← h2, E.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm⟩

/-- **A curve contracted by a birational morphism lies in its exceptional set.** -/
private theorem point_mem_exceptionalSet_of_isContractedBy {X X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] (q : X ⟶ X') (C : ProperCurve sX)
    (hC : C.IsContractedBy q) : C.point ∈ (MMP.Mori.exceptionalSet q : Set X) := by
  by_contra hη
  set V := biregularLocus q
  have hV : C.point ∈ q ⁻¹ᵁ V := by simpa [MMP.Mori.mem_exceptionalSet] using hη
  have hiso : IsIso (q ∣_ V) := isBiregular_biregularLocus q
  have hopen : IsOpenImmersion ((q ⁻¹ᵁ V).ι ≫ q) := by
    rw [← morphismRestrict_ι]; infer_instance
  exact not_isContractedBy_of_injOn_of_mem q _ (injOn_of_isOpenImmersion q _) C hV hC

/-- **The only curve contracted by a divisorial contraction of a surface is its exceptional
curve.** If the exceptional set of `q` is the support of a prime divisor `E`, every proper curve
contracted by `q` has generic point `η_E`. -/
private theorem point_eq_of_isContractedBy {X X' : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] (hdim : topologicalKrullDim X = 2)
    (q : X ⟶ X') {E : MMP.Mori.PrimeDivisor X}
    (hE : (MMP.Mori.exceptionalSet q : Set X) = E.support) (C : ProperCurve sX)
    (hC : C.IsContractedBy q) : C.point = E.genericPoint := by
  have h1 := point_mem_exceptionalSet_of_isContractedBy q C hC
  rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  have hsp : E.genericPoint ⤳ C.point := specializes_iff_mem_closure.mpr h1
  by_contra hne
  have hlt : C.point < E.genericPoint :=
    lt_of_le_not_ge hsp fun h => hne (Specializes.antisymm h hsp).eq
  have h2 := Order.coheight_strictAnti hlt
    (lt_of_le_of_lt (coheight_le_of_topologicalKrullDim_le hdim.le _) (by decide))
  rw [E.coheight_genericPoint, coheight_point_eq_one sX hdim C] at h2
  exact lt_irrefl _ h2

end Exceptional

/-- A separated `ℂ`-scheme is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsSeparated sX] :
    IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- Coefficients of a push-forward along a proper birational morphism: every prime divisor `P` of
the target is the image of a prime divisor `E` of the source, and `(q_* D)_P = D_E`. -/
private theorem exists_transformDivisor_apply {X X' : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX' : X' ⟶ Spec (.of ℂ)}
    (hX' : IsNormalVariety ℂ sX') (q : X ⟶ X') [IsProper q] (hX : IsNormalVariety ℂ (q ≫ sX'))
    (hqb : IsBirationalMorphism q) (P : MMP.Mori.PrimeDivisor X') :
    ∃ E : MMP.Mori.PrimeDivisor X, q E.genericPoint = P.genericPoint ∧ ∀ {R : Type} [AddCommMonoid R]
      (D : DivisorWithCoeffs R X), RationalMap.transformDivisor (X := X) q.toRationalMap D P = D E := by
  obtain ⟨E, heq, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX' hX hqb P
  exact ⟨E, heq, fun D => htr D⟩

/-- **The data of a divisorial step.** Let `q : X ⟶ X'` be a proper birational morphism over `Y`
onto a `ℚ`-factorial variety, and `(X, B_X)` a model of the program with lowered boundary `L`.
Then `(X', q_* B_X)` is crepant for `q`, and is again a model of the program with lowered
boundary `q_* L`. -/
private theorem divisorial_step {X X' Y : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} (hQ' : IsQFactorial sX')
    (q : X ⟶ X') [IsProper q] (hqs : q ≫ sX' = sX) (hqb : IsBirationalMorphism q)
    {π : X ⟶ Y} (π' : X' ⟶ Y) [IsDominant π'] (hqπ : q ≫ π' = π) {A : QDivisor Y}
    (hAq : A.IsQCartier) {ε : ℚ} {KX : Divisor X} {KX' : Divisor X'} {BX L : QDivisor X}
    {c0ne c0vert : Prop} (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hKX' : ∃ m : ℕ, KX'.IsCanonicalDivisor sX' m) (hinv : ModelInv sX π hAq ε KX BX L c0ne c0vert)
    (hne : c0ne → (RationalMap.transformDivisor (X := X) q.toRationalMap BX).roundDown ≠ 0) :
    (∀ (hqY : IsNormalVariety ℂ (q ≫ sX')) (hq : IsBirationalMorphism q),
      MMP.Mori.IsCrepantBoundary sX' 2 KX'
        (RationalMap.transformDivisor (X := X) q.toRationalMap BX) q hqY hq BX) ∧
    ModelInv sX' π' hAq ε KX' (RationalMap.transformDivisor (X := X) q.toRationalMap BX)
      (RationalMap.transformDivisor (X := X) q.toRationalMap L) c0ne c0vert := by
  classical
  subst hqs hqπ
  have hX' : IsNormalVariety ℂ sX' := hQ'.1
  have hX : IsNormalVariety ℂ (q ≫ sX') := hinv.lc.1.1
  haveI := hqb.isDominant
  haveI : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sX') := hX.1.toLocallyOfFiniteType
  haveI := hX'.1
  haveI := hX.1
  have hdim := hinv.dim
  have hdim' : topologicalKrullDim X' = 2 := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' (q ≫ sX') hqb]
    exact hdim
  have hKX2 := isCanonicalDivisor_two hdim hKX
  have hKX'2 := isCanonicalDivisor_two hdim' hKX'
  obtain ⟨hη, hadj⟩ := hinv.adj
  have hη' : ∀ Z : irreducibleComponents X', π' (componentGenericPoint X' Z) ∉ A.supp :=
    fun Z => MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' π' A Z
  obtain ⟨ω, hω0, hωX', hωX, hlin, hB, hpb⟩ :=
    crepant_step hX' hQ' q hX hqb π' hAq hη hη' hKX2 hadj
  set B' := RationalMap.transformDivisor (X := X) q.toRationalMap BX
  -- `div ω` is a canonical divisor of `X'`, linearly equivalent to `K_{X'}`
  have hωK : (divisorOfForm ω).LinearlyEquivalent KX' := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX' hKX'2 hω0 (m := 1)
  have hKV : (divisorOfForm ω).IsCanonicalDivisor sX' 2 := hKX'2.of_linearlyEquivalent hωK
  have hNq : (Divisor.toQDivisor (divisorOfForm ω) + B').IsQCartier :=
    isQCartier_of_isQFactorial sX' hQ' _
  -- crepancy
  have hcrep : MMP.Mori.IsCrepantBoundary sX' 2 (divisorOfForm ω) B' q hX hqb BX :=
    MMP.Threefold.Mori.isCrepantBoundary_of_add_eq_pullback ⟨hX', hKV, hNq⟩ q hX hqb hKX2
      hωX'.symm ⟨hB, hpb⟩
  have hB'0 : ∀ P, 0 ≤ B'.coeff P := fun P => by
    obtain ⟨E, -, htr⟩ := exists_transformDivisor_apply hX' q hX hqb P
    change 0 ≤ RationalMap.transformDivisor (X := X) q.toRationalMap BX P
    rw [htr]
    exact hinv.lc.2.1 E
  refine ⟨fun hqY hq => ?_, ?_⟩
  · exact isCrepantBoundary_of_linearlyEquivalent hcrep hωK
  refine
    { lowered := ?_
      lc := ?_
      dim := hdim'
      adj := ⟨hη', ?_⟩
      ne := hne
      dom := inferInstance
      vert := ?_
      horiz := ?_ }
  · -- the lowered boundary
    rw [hinv.lowered]
    refine Finsupp.ext fun P => ?_
    obtain ⟨E, -, htr⟩ := exists_transformDivisor_apply hX' q hX hqb P
    rw [htr]
    change (BX - ε • Divisor.toQDivisor BX.roundDown).coeff E =
      (B' - ε • Divisor.toQDivisor B'.roundDown).coeff P
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
      DivisorWithCoeffs.coeff_roundDown, smul_eq_mul]
    change BX E - ε * ⌊BX E⌋ = RationalMap.transformDivisor (X := X) q.toRationalMap BX P -
      ε * ⌊RationalMap.transformDivisor (X := X) q.toRationalMap BX P⌋
    rw [htr]
  · rw [← hωX] at hpb
    exact isLogCanonicalPair_of_isPullback hX' hQ' q hX hqb hω0 hKV (hωX ▸ hKX2) hB'0 hpb
      hinv.lc
  · obtain ⟨φ, hφ⟩ := hωK
    refine QDivisor.QLinearlyEquivalent.trans ⟨1, one_pos, φ⁻¹, ?_⟩ hlin
    rw [MMP.Mori.principalDivisor_inv, ← hφ, map_neg, map_sub, Nat.cast_one, one_smul]
    abel
  · -- verticality of the floor is preserved
    intro hc P hP x hx
    have hvert := hinv.vert hc
    obtain ⟨E, hEP, htr⟩ := exists_transformDivisor_apply hX' q hX hqb P
    have hE : (Divisor.toQDivisor BX.roundDown) E ≠ 0 := by
      intro h0
      apply hP
      have h1 : (Divisor.toQDivisor BX.roundDown).coeff E = 0 := h0
      change (Divisor.toQDivisor B'.roundDown).coeff P = 0
      rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown] at h1 ⊢
      change ((⌊RationalMap.transformDivisor (X := X) q.toRationalMap BX P⌋ : ℤ) : ℚ) = 0
      rw [htr]
      exact h1
    rw [support_eq_image_of_map_genericPoint_eq q hEP] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hvert E hE y hy
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, hEP]
  · -- horizontality of the floor is preserved
    intro hc hv'
    apply hinv.horiz hc
    intro E hE x hx
    simp only [Scheme.Hom.comp_apply]
    by_cases hexc : E.genericPoint ∈ (MMP.Mori.exceptionalSet q : Set X)
    · have hx' : x ∈ closure ({E.genericPoint} : Set X) := by
        rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
      rw [map_eq_of_mem_closure_of_mem_exceptionalSet hX' hdim' hX.1 hqb hexc hx']
    · obtain ⟨P, hEP⟩ := exists_map_genericPoint_eq_of_notMem_exceptionalSet q hexc
      haveI : IsSeparated sX' := hX'.1.toIsSeparated
      haveI := isSeparated_toTerminal sX'
      haveI : IsSeparated q := IsSeparated.of_comp q sX'
      have hP : (Divisor.toQDivisor B'.roundDown) P ≠ 0 := by
        intro h0
        apply hE
        have h1 : (Divisor.toQDivisor B'.roundDown).coeff P = 0 := h0
        change (Divisor.toQDivisor BX.roundDown).coeff E = 0
        rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown] at h1 ⊢
        change ((⌊RationalMap.transformDivisor (X := X) q.toRationalMap BX P⌋ : ℤ) : ℚ) = 0 at h1
        rwa [MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hqb hEP] at h1
      have hqx : q x ∈ (P.support : Set X') := by
        rw [support_eq_image_of_map_genericPoint_eq q hEP]
        exact ⟨x, hx, rfl⟩
      rw [hv' P hP (q x) hqx, hEP]

/-- **The floor survives a divisorial step.** Let `q : X ⟶ X'` be a proper birational morphism
of `ℚ`-factorial projective surfaces over `Y` with exceptional set a prime divisor `E`, and
`(X, B_X)` a model of the program on which `K + L` is negative on the curves contracted by `q`.
If the floor of `B_X` is nonzero, so is the floor of `q_* B_X`: a floor component other than `E`
survives, and if `E` were the whole floor then `E · E > 0`, so `E` would be `q`-nef and the
negativity lemma would make `-E` effective. -/
private theorem roundDown_transformDivisor_ne_zero {X X' Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    (hQ' : IsQFactorial sX') (hQ : IsQFactorial sX) (hXp : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hYv : MMP.Mori.IsVariety ℂ sY) (q : X ⟶ X') [IsProper q] (hqs : q ≫ sX' = sX)
    (hqb : IsBirationalMorphism q) {π : X ⟶ Y} (π' : X' ⟶ Y) (hπ' : π' ≫ sY = sX')
    (hqπ : q ≫ π' = π) {A : QDivisor Y} (hAq : A.IsQCartier) {ε : ℚ} (hε : 0 < ε ∧ ε < 1)
    {KX : Divisor X} {BX L : QDivisor X} {c0ne c0vert : Prop}
    (hinv : ModelInv sX π hAq ε KX BX L c0ne c0vert) {E : MMP.Mori.PrimeDivisor X}
    (hE : (MMP.Mori.exceptionalSet q : Set X) = E.support)
    (hneg : ∀ C : ProperCurve sX, C.IsContractedBy q → ∀ hD : (Divisor.toQDivisor KX + L).IsQCartier,
      (Divisor.toQDivisor KX + L).intersectionNumber ℂ sX C.ι C.dim_le hD < 0)
    (hne : BX.roundDown ≠ 0) :
    (RationalMap.transformDivisor (X := X) q.toRationalMap BX).roundDown ≠ 0 := by
  classical
  subst hqs hqπ
  have hX' : IsNormalVariety ℂ sX' := hQ'.1
  have hX : IsNormalVariety ℂ (q ≫ sX') := hQ.1
  haveI := hqb.isDominant
  haveI : LocallyOfFiniteType (q ≫ sX') := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact (q ≫ sX') := hX.1.toQuasiCompact
  haveI : IsProper (q ≫ sX') := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp
    ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hXp).2).2
  haveI : IsSeparated sX' := hX'.1.toIsSeparated
  haveI := isSeparated_toTerminal sX'
  haveI : IsSeparated q := IsSeparated.of_comp q sX'
  haveI := hX'.1
  haveI := hX.1
  have hdim := hinv.dim
  have hdim' : topologicalKrullDim X' = 2 := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' (q ≫ sX') hqb]
    exact hdim
  have hηE : E.genericPoint ∈ (MMP.Mori.exceptionalSet q : Set X) := by
    rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  intro hz
  -- every floor component is `E`
  have hfloor : ∀ E₁ : MMP.Mori.PrimeDivisor X, BX.roundDown E₁ ≠ 0 → E₁ = E := by
    intro E₁ h1
    by_contra hne1
    have hη1 : E₁.genericPoint ∉ (MMP.Mori.exceptionalSet q : Set X) := by
      intro hmem
      rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
      have hsp : E.genericPoint ⤳ E₁.genericPoint := specializes_iff_mem_closure.mpr hmem
      have hlt : E₁.genericPoint < E.genericPoint := lt_of_le_not_ge hsp fun h =>
        hne1 (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (Specializes.antisymm h hsp).eq)
      have h2 := Order.coheight_strictAnti hlt (by rw [E.coheight_genericPoint]; decide)
      rw [E.coheight_genericPoint, E₁.coheight_genericPoint] at h2
      exact lt_irrefl _ h2
    obtain ⟨P, hEP⟩ := exists_map_genericPoint_eq_of_notMem_exceptionalSet q hη1
    have h3 : (RationalMap.transformDivisor (X := X) q.toRationalMap BX).roundDown.coeff P = 0 := by
      rw [hz]; rfl
    rw [DivisorWithCoeffs.coeff_roundDown] at h3
    change ⌊RationalMap.transformDivisor (X := X) q.toRationalMap BX P⌋ = 0 at h3
    rw [MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hqb hEP] at h3
    apply h1
    change BX.roundDown.coeff E₁ = 0
    rw [DivisorWithCoeffs.coeff_roundDown]
    exact h3
  -- the floor is `E`
  have h0E : ∀ E₁, 0 ≤ BX.coeff E₁ := hinv.lc.2.1
  have h1E : ∀ E₁, BX.coeff E₁ ≤ 1 := coeff_le_one_of_isLogCanonicalPair hinv.lc
  have hfl := fun E₁ => floor_eq_ite (h0E E₁) (h1E E₁)
  set G : QDivisor X := Divisor.toQDivisor (Finsupp.single E 1)
  have hGfl : Divisor.toQDivisor BX.roundDown = G := by
    obtain ⟨E₁, hE₁⟩ := Finsupp.ne_iff.mp hne
    have hE₁E := hfloor E₁ hE₁
    subst hE₁E
    have hc1 : BX.coeff E₁ = 1 := by
      by_contra hc
      apply hE₁
      change BX.roundDown.coeff E₁ = 0
      rw [DivisorWithCoeffs.coeff_roundDown, Int.floor_eq_zero_iff.mpr ⟨h0E E₁,
        lt_of_le_of_ne (h1E E₁) hc⟩]
    refine Finsupp.ext fun E₂ => ?_
    change (Divisor.toQDivisor BX.roundDown).coeff E₂ = G.coeff E₂
    rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown, hfl, Divisor.coeff_toQDivisor]
    by_cases h : E₂ = E₁
    · subst h; simp [hc1, DivisorWithCoeffs.coeff_apply]
    · have : ¬ BX.coeff E₂ = 1 := fun h' => by
        have := hfloor E₂ (by
          change BX.roundDown.coeff E₂ ≠ 0
          rw [DivisorWithCoeffs.coeff_roundDown, show BX.coeff E₂ = 1 from h']; simp)
        exact h this
      have this' : ¬ BX E₂ = 1 := this
      simp [this', DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Ne.symm h]
  -- the exceptional curve
  let CE : ProperCurve (q ≫ sX') := ⟨E.genericPoint, isProperCurve_genericPoint _ hdim E⟩
  have hCE : CE.IsContractedBy q := fun x hx =>
    map_eq_of_mem_closure_of_mem_exceptionalSet hX' hdim' hX.1 hqb hηE hx
  have hqf := fun D : QDivisor X => isQCartier_of_isQFactorial (q ≫ sX') hQ D
  have hlt := hneg CE hCE (hqf _)
  rw [hinv.intersectionNumber_eq hQ hYv (by rw [Category.assoc, hπ']) CE (fun x hx => by
      simp only [Scheme.Hom.comp_apply]; rw [hCE x hx]),
    intersectionNumber_congr (k := ℂ) (q ≫ sX') CE.ι CE.dim_le _ (hqf G) hGfl] at hlt
  have hGpos : 0 < G.intersectionNumber ℂ (q ≫ sX') CE.ι CE.dim_le (hqf G) := by
    nlinarith [hε.1]
  -- `G = E` is nef over `X'`
  have hnef : (-(-G)).IsRelativelyNef (q ≫ sX') q := by
    rw [neg_neg]
    refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (q ≫ sX') (hqf G)
      fun C hC => ?_
    have hCp := point_eq_of_isContractedBy hdim q hE C hC
    obtain ⟨pt, hpt⟩ := C
    change pt = E.genericPoint at hCp
    subst hCp
    exact hGpos.le
  -- `q_* (-G) = 0`
  have hEnone : RationalMap.transformPrimeDivisor (X := X) q.toRationalMap E = none := by
    rcases h : RationalMap.transformPrimeDivisor (X := X) q.toRationalMap E with _ | P
    · rfl
    · exfalso
      have hEP := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q E P).mp h
      have := P.isDiscreteValuationRing_localRing
      have : ValuationRing (X'.presheaf.stalk (q E.genericPoint)) := by
        rw [hEP]; exact inferInstanceAs (ValuationRing P.localRing)
      exact hηE (mem_biregularLocus_of_valuationRing hX' hX.1 hqb _)
  have heff : (RationalMap.transformDivisor (X := X) q.toRationalMap (-G)).IsEffective := by
    rw [map_neg, transformDivisor_toQDivisor hX' q hX hqb,
      RationalMap.transformDivisor_single_of_eq_none hEnone, map_zero, neg_zero]
    intro E₁; simp
  have hGeff := MMP.Mori.QDivisor.isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor
    ℂ sX' (q ≫ sX') hX' hX hdim' hdim q rfl hqb (hqf _) hnef heff
  have h2 := hGeff E
  have h3 : (Divisor.toQDivisor (Finsupp.single E (1 : ℤ) : Divisor X)) E = 1 := by
    change (((Finsupp.single E (1 : ℤ) : Divisor X) E : ℤ) : ℚ) = 1
    simp
  change 0 ≤ (-G) E at h2
  rw [Finsupp.neg_apply, h3] at h2
  linarith

/-! ### Log resolutions: pure codimension one and snc subsets -/

namespace LogRes

universe u

open Topology

section Topology

variable {A T : Type*} [TopologicalSpace A] [TopologicalSpace T] {ψ : A → T}

/-- The closure of the image of an irreducible closed subset under an open embedding. -/
private def closureImage (hψ : IsOpenEmbedding ψ) (Z : IrreducibleCloseds A) :
    IrreducibleCloseds T :=
  ⟨closure (ψ '' Z), (Z.isIrreducible.image ψ hψ.continuous.continuousOn).closure,
    isClosed_closure⟩

/-- The preimage of an irreducible closed subset meeting the image of an open embedding. -/
private def preimageIrr (hψ : IsOpenEmbedding ψ) (B : IrreducibleCloseds T)
    (hne : ((B : Set T) ∩ Set.range ψ).Nonempty) : IrreducibleCloseds A :=
  ⟨ψ ⁻¹' B, B.isIrreducible.preimage hψ hne, B.isClosed.preimage hψ.continuous⟩

private lemma preimage_closureImage (hψ : IsOpenEmbedding ψ) (Z : IrreducibleCloseds A) :
    ψ ⁻¹' (closureImage hψ Z : Set T) = Z := by
  change ψ ⁻¹' closure (ψ '' Z) = Z
  rw [← hψ.isInducing.closure_eq_preimage_closure_image, Z.isClosed.closure_eq]

private lemma closureImage_preimageIrr (hψ : IsOpenEmbedding ψ) (B : IrreducibleCloseds T)
    (hne : ((B : Set T) ∩ Set.range ψ).Nonempty) :
    closureImage hψ (preimageIrr hψ B hne) = B := by
  have hne' : (ψ ⁻¹' B).Nonempty := by obtain ⟨_, hb, x, rfl⟩ := hne; exact ⟨x, hb⟩
  exact SetLike.coe_injective <| closure_image_preimage_of_isPreirreducible ψ hψ.isOpenMap B
    hne' B.isIrreducible.isPreirreducible B.isClosed

/-- Taking closures of images along an open embedding preserves codimension. -/
private lemma codimension_closureImage (hψ : IsOpenEmbedding ψ) (Z : IrreducibleCloseds A) :
    codimension (closureImage hψ Z) = codimension Z := by
  rw [codimension_eq_coheight, codimension_eq_coheight]
  have hmono : StrictMono (closureImage hψ) := fun a b hab ↦
    lt_of_le_of_ne (closure_mono (Set.image_mono hab.le)) fun h ↦ hab.ne <|
      SetLike.coe_injective <| by
        simpa only [preimage_closureImage] using
          congrArg (fun W : IrreducibleCloseds T ↦ ψ ⁻¹' (W : Set T)) h
  refine (Order.coheight_eq_of_strictMono _ hmono (fun a B hab ↦ ?_) Z).symm
  have hne : ((B : Set T) ∩ Set.range ψ).Nonempty := by
    obtain ⟨x, hx⟩ := a.isIrreducible.nonempty
    exact ⟨ψ x, hab.le (subset_closure ⟨x, hx, rfl⟩), x, rfl⟩
  refine ⟨preimageIrr hψ B hne, lt_of_le_of_ne (fun x hx ↦ hab.le (subset_closure ⟨x, hx, rfl⟩))
    ?_, closureImage_preimageIrr hψ B hne⟩
  rintro rfl
  exact hab.ne (closureImage_preimageIrr hψ B hne)

end Topology

private lemma isPreirreducible_preimage_val {Y : Type*} [TopologicalSpace Y] {C W : Set Y}
    (hW : IsPreirreducible W) (hWC : W ⊆ C) : IsPreirreducible (Subtype.val ⁻¹' W : Set C) := by
  rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨y, hyW, hyu, hyv⟩ := hW u' v' hu' hv' ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  exact ⟨⟨y, hWC hyW⟩, hyW, hyu, hyv⟩

/-- An irreducible closed set contained in a closed set lies in an irreducible closed subset
maximal in it. -/
private lemma exists_maximal_ge {Y : Type*} [TopologicalSpace Y] {C : Set Y} (hC : IsClosed C)
    (Z : IrreducibleCloseds Y) (hZ : (Z : Set Y) ⊆ C) :
    ∃ W : IrreducibleCloseds Y, Maximal (fun W' : IrreducibleCloseds Y ↦ (W' : Set Y) ⊆ C) W ∧
      Z ≤ W := by
  obtain ⟨t, ht, hxt, hmax⟩ := exists_preirreducible (Subtype.val ⁻¹' (Z : Set Y) : Set C)
    (isPreirreducible_preimage_val Z.isIrreducible.isPreirreducible hZ)
  obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
  let W : IrreducibleCloseds Y := ⟨closure (Subtype.val '' t),
    (IsIrreducible.closure ⟨⟨z, ⟨z, hZ hz⟩, hxt hz, rfl⟩,
      ht.image _ continuous_subtype_val.continuousOn⟩), isClosed_closure⟩
  have hWC : (W : Set Y) ⊆ C := closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact y.2) hC
  refine ⟨W, ⟨hWC, fun W' hW'C hWW' y hy ↦ ?_⟩, fun y hy ↦ subset_closure ⟨⟨y, hZ hy⟩, hxt hy, rfl⟩⟩
  have := hmax _ (isPreirreducible_preimage_val W'.isIrreducible.isPreirreducible hW'C)
    fun y hy ↦ hWW' (subset_closure ⟨y, hy, rfl⟩)
  have : (⟨y, hW'C hy⟩ : C) ∈ t := by rw [← this]; exact hy
  exact subset_closure ⟨_, this, rfl⟩

/-- If `C₁ ⊆ Y` is closed of pure codimension one, `h` is an open embedding on the complement
`U` of `C₁`, and `T` is closed of pure codimension one, then so is `C₁ ∪ h⁻¹(T)`. -/
private lemma isPureCodimOne_sup_preimage {Y X' : Type*} [TopologicalSpace Y]
    [TopologicalSpace X'] {h : Y → X'} (hh : Continuous h) {U : Set Y} (hU : IsOpen U)
    (hψ : IsOpenEmbedding (U.restrict h)) {C₁ : Closeds Y} (hUC : Uᶜ ⊆ C₁)
    (hC₁ : IsPureCodimOne C₁) {T : Closeds X'} (hT : IsPureCodimOne T) :
    IsPureCodimOne (C₁ ⊔ T.preimage hh) := by
  intro W hW
  have hWsub : (W : Set Y) ⊆ (C₁ : Set Y) ∪ h ⁻¹' T := hW.1
  by_cases hWC : (W : Set Y) ⊆ C₁
  · exact hC₁ W ⟨hWC, fun W' hW' hle ↦ hW.2 (hW'.trans fun y hy ↦ Or.inl hy) hle⟩
  obtain ⟨w, hwW, hwC⟩ := Set.not_subset.mp hWC
  have hwU : w ∈ U := by by_contra hw; exact hwC (hUC hw)
  have hWT : (W : Set Y) ⊆ h ⁻¹' T :=
    ((isPreirreducible_iff_isClosed_union_isClosed.mp W.isIrreducible.isPreirreducible)
      _ _ C₁.isClosed (T.isClosed.preimage hh) hWsub).resolve_left hWC
  have hι : IsOpenEmbedding (Subtype.val : U → Y) := hU.isOpenEmbedding_subtypeVal
  let WU := preimageIrr hι W ⟨w, hwW, ⟨w, hwU⟩, rfl⟩
  have hWU : closureImage hι WU = W := closureImage_preimageIrr hι W _
  let Z := closureImage hψ WU
  have hZmax : Maximal (fun Z' : IrreducibleCloseds X' ↦ (Z' : Set X') ⊆ T) Z := by
    refine ⟨closure_minimal (by rintro _ ⟨u, hu, rfl⟩; exact hWT hu) T.isClosed,
      fun Z' hZ'T hZZ' ↦ ?_⟩
    let ZU := preimageIrr hψ Z'
      ⟨h w, hZZ' (subset_closure ⟨⟨w, hwU⟩, hwW, rfl⟩), ⟨w, hwU⟩, rfl⟩
    have hW'sub : (closureImage hι ZU : Set Y) ⊆ (C₁ : Set Y) ∪ h ⁻¹' T :=
      (closure_minimal (by rintro _ ⟨u, hu, rfl⟩; exact hZ'T hu)
        (T.isClosed.preimage hh)).trans fun y hy ↦ Or.inr hy
    have hle : W ≤ closureImage hι ZU := by
      rw [← hWU]
      exact closure_mono (Set.image_mono fun u hu ↦ hZZ' (subset_closure ⟨u, hu, rfl⟩))
    have hle' := hW.2 hW'sub hle
    rw [← closureImage_preimageIrr hψ Z' _]
    refine closure_mono (Set.image_mono fun u hu ↦ hle' ?_)
    change u ∈ Subtype.val ⁻¹' (closureImage hι ZU : Set Y)
    rw [preimage_closureImage]; exact hu
  rw [← hWU, codimension_closureImage hι WU, ← codimension_closureImage hψ WU]
  exact hT Z hZmax

section SNC

/-- The support of a prime divisor, as an irreducible closed subset. -/
private noncomputable def primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    IrreducibleCloseds X :=
  IrreducibleCloseds.closureSingleton E.genericPoint

private lemma coe_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    (primeIrr E : Set X) = E.support := by
  rw [E.support_eq_closure]; rfl

private lemma codimension_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    codimension (primeIrr E) = 1 := E.codimension_one

private lemma exists_mem_of_subset_iUnion {X : Scheme.{u}}
    {s : Finset (AlgebraicGeometry.PrimeDivisor X)}
    (W : IrreducibleCloseds X) (hW : (W : Set X) ⊆ ⋃ E ∈ s, E.support) :
    ∃ E ∈ s, W ≤ primeIrr E := by
  classical
  obtain ⟨z, hz, hWz⟩ := (isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible)
    (s.image AlgebraicGeometry.PrimeDivisor.support)
    (by
      intro z hz
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← coe_primeIrr]; exact (primeIrr E).isClosed)
    (by
      intro x hx
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp (hW hx)
      exact ⟨E.support, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hE), hxE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨E, hE, fun x hx ↦ by
    change x ∈ (primeIrr E : Set X); rw [coe_primeIrr]; exact hWz hx⟩

variable {k : Type u} [Field k]

/-- A closed subset of pure codimension one of an snc divisor is an snc divisor. -/
private lemma isSNCSubset_of_le {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {S C : Closeds X}
    (hS : IsSNCSubset sX S) (hC : IsPureCodimOne C) (hCS : C ≤ S) : IsSNCSubset sX C := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · exact Or.inl (le_bot_iff.mp hCS)
  right
  refine ⟨s.filter (fun E ↦ E.support ⊆ C), ?_, ?_⟩
  · apply subset_antisymm
    · intro x hx
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx
      exact (Finset.mem_filter.mp hE).2 hxE
    · intro x hx
      obtain ⟨W, hW, hxW⟩ := exists_maximal_ge C.isClosed
        (IrreducibleCloseds.closureSingleton x) (by
          change closure {x} ⊆ (C : Set X)
          exact closure_minimal (by simpa using hx) C.isClosed)
      have hxW' : x ∈ (W : Set X) := hxW (subset_closure rfl)
      obtain ⟨E, hE, hWE⟩ := exists_mem_of_subset_iUnion W (hs ▸ hW.1.trans hCS)
      have hWE' : W = primeIrr E := by
        by_contra hne
        have hlt : W < primeIrr E := lt_of_le_of_ne hWE hne
        have := Order.coheight_add_one_le hlt
        rw [← codimension_eq_coheight, ← codimension_eq_coheight, codimension_primeIrr,
          hC W hW] at this
        exact absurd this (by decide)
      refine Set.mem_iUnion₂.mpr ⟨E, Finset.mem_filter.mpr ⟨hE, ?_⟩, ?_⟩
      · rw [← coe_primeIrr, ← hWE']; exact hW.1
      · rw [← coe_primeIrr, ← hWE']; exact hxW'
  · refine hsnc.of_support_subset ?_
    intro E hE
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hE ⊢
    simp only [Finsupp.single_apply] at hE ⊢
    rw [Finset.sum_ite_eq'] at hE ⊢
    split_ifs at hE with h1
    · rw [if_pos (Finset.mem_filter.mp h1).1]; exact one_ne_zero
    · exact absurd rfl hE

end SNC

section Exceptional

/-- If `a ≫ b` is an isomorphism, `a` is dominant, the source of `b` is reduced and `b` is
separated, then `b` is an isomorphism. -/
private lemma isIso_of_isIso_comp {A B V : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ V) [IsIso (a ≫ b)]
    [IsDominant a] [IsReduced B] [IsSeparated b] : IsIso b := by
  refine ⟨⟨inv (a ≫ b) ≫ a, ?_, by simp⟩⟩
  refine ext_of_isDominant_of_isSeparated b ?_ a ?_
  · simp
  · rw [← Category.assoc, IsIso.hom_inv_id_assoc, Category.comp_id]

/-- If `h ≫ g` is an isomorphism over `V`, with `h` dominant, `X'` reduced and `g` separated,
then `g` is an isomorphism over `V` and `h` over `g⁻¹(V)`. -/
private lemma isBiregular_of_isBiregular_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] {V : X.Opens}
    (hV : IsBiregular (h ≫ g) V) : IsBiregular g V ∧ IsBiregular h (g ⁻¹ᵁ V) := by
  unfold IsBiregular at hV ⊢
  rw [morphismRestrict_comp] at hV
  have : IsDominant (h ∣_ g ⁻¹ᵁ V) := IsZariskiLocalAtTarget.restrict ‹IsDominant h› _
  have : IsSeparated (g ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsSeparated g› _
  have := @isIso_of_isIso_comp _ _ _ (h ∣_ g ⁻¹ᵁ V) (g ∣_ V) hV _ _ _
  exact ⟨this, @IsIso.of_isIso_comp_right _ _ _ _ _ _ (g ∣_ V) this hV⟩

/-- The exceptional set of a composite. -/
private lemma exceptionalSet_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] [UniversallyClosed g] :
    MMP.Mori.exceptionalSet (h ≫ g) = MMP.Mori.exceptionalSet h ⊔ (MMP.Mori.exceptionalSet g).preimage h.continuous := by
  apply SetLike.coe_injective
  ext y
  change y ∈ MMP.Mori.exceptionalSet (h ≫ g) ↔ y ∈ MMP.Mori.exceptionalSet h ∨ h y ∈ MMP.Mori.exceptionalSet g
  simp only [mem_exceptionalSet]
  constructor
  · intro hy
    by_contra hne
    push Not at hne
    obtain ⟨hyh, hyg⟩ := hne
    apply hy
    have hcl : IsClosed (g '' (biregularLocus h : Set X')ᶜ) :=
      g.isClosedMap _ (biregularLocus h).isOpen.isClosed_compl
    let W : X.Opens := biregularLocus g ⊓ ⟨_, hcl.isOpen_compl⟩
    have hWg : IsBiregular g W :=
      isBiregular_iff_le_biregularLocus.mpr inf_le_left
    have hWh : IsBiregular h (g ⁻¹ᵁ W) := by
      refine isBiregular_iff_le_biregularLocus.mpr ?_
      intro x hx
      by_contra hxU
      exact hx.2 ⟨x, hxU, rfl⟩
    have hiso : IsBiregular (h ≫ g) W := by
      unfold IsBiregular at *
      rw [morphismRestrict_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hWh hWg
    refine le_biregularLocus hiso ⟨hyg, ?_⟩
    rintro ⟨x, hx, hxy⟩
    have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
    have hxy' : g x = g (h y) := hxy.trans (Scheme.Hom.comp_apply h g y)
    have hx' : g x ∈ biregularLocus g := hxy' ▸ hyg
    have hinj := (g ∣_ biregularLocus g).isOpenEmbedding.injective
      (a₁ := (⟨x, hx'⟩ : g ⁻¹ᵁ biregularLocus g)) (a₂ := ⟨h y, hyg⟩)
    have : x = h y := congrArg Subtype.val (hinj (Subtype.ext
      ((morphismRestrict_base_coe g _ _).trans (hxy'.trans
        (morphismRestrict_base_coe g (biregularLocus g) ⟨h y, hyg⟩).symm))))
    exact hx (this ▸ hyh)
  · intro hy hmem
    have hb := isBiregular_of_isBiregular_comp h g (isBiregular_biregularLocus (h ≫ g))
    rcases hy with hy | hy
    · exact hy (le_biregularLocus hb.2 hmem)
    · exact hy (le_biregularLocus hb.1 hmem)

end Exceptional

section Birational

/-- A birational morphism is an open immersion with dense image on a dense open subset. -/
private lemma exists_of_isBirationalMorphism {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ S : X.Opens, Dense (S : Set X) ∧ IsOpenImmersion (S.ι ≫ f) ∧ IsDominant (S.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  have hWe' : W ≤ e.source := hWe
  have heq : W.ι ≫ f = X.homOfLE hWe' ≫ e.iso.hom ≫ e.target.ι := by
    simp only [Scheme.PartialMap.restrict, Scheme.PartialMap.mk.injEq, heq_eq_eq, true_and,
      Scheme.PartialIso.toPartialMap_hom, Scheme.Hom.toPartialMap_hom] at h
    rw [Scheme.topIso_hom] at h
    refine Eq.trans ?_ h.symm
    exact (Scheme.homOfLE_ι_assoc X (le_top : W ≤ ⊤) f).symm
  have h₁ : IsDominant (X.homOfLE hWe') := by
    have : IsDominant (X.homOfLE hWe' ≫ e.source.ι) := by
      rw [Scheme.homOfLE_ι]; exact Opens.isDominant_ι hW
    exact IsDominant.of_comp_of_isOpenImmersion (X.homOfLE hWe') e.source.ι
  refine ⟨W, hW, ?_, ?_⟩
  · rw [heq]; infer_instance
  · rw [heq]
    have := Opens.isDominant_ι e.dense_target
    infer_instance

/-- A morphism which is an open immersion with dense image on a dense open is birational. -/
private lemma isBirationalMorphism_of_exists {X Y : Scheme.{u}} (f : X ⟶ Y) (S : X.Opens)
    (hS : Dense (S : Set X)) [IsOpenImmersion (S.ι ≫ f)] (hd : IsDominant (S.ι ≫ f)) :
    IsBirationalMorphism f := by
  let e : X.PartialIso Y :=
    { source := S
      dense_source := hS
      target := (S.ι ≫ f).opensRange
      dense_target := by
        rw [Scheme.Hom.coe_opensRange]
        exact (hd.denseRange : _)
      iso := (S.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨S, hS, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  rw [Scheme.topIso_hom]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans (Scheme.homOfLE_ι_assoc _ _ _).symm

/-- A composite of birational morphisms is birational. -/
private lemma isBirationalMorphism_comp {Y X' X : Scheme.{u}} {h : Y ⟶ X'} {g : X' ⟶ X}
    (hh : IsBirationalMorphism h) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (h ≫ g) := by
  obtain ⟨Sh, hSh, hoh, hdh⟩ := exists_of_isBirationalMorphism hh
  obtain ⟨Sg, hSg, hog, hdg⟩ := exists_of_isBirationalMorphism hg
  let S : Y.Opens := Sh ⊓ h ⁻¹ᵁ Sg
  have hSS : S ≤ Sh := inf_le_left
  have hle : S ≤ h ⁻¹ᵁ Sg := inf_le_right
  have hres : h.resLE Sg S hle ≫ Sg.ι = Y.homOfLE hSS ≫ Sh.ι ≫ h := by
    rw [Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
  have : IsOpenImmersion (h.resLE Sg S hle ≫ Sg.ι) := by rw [hres]; infer_instance
  have : IsOpenImmersion (h.resLE Sg S hle) := IsOpenImmersion.of_comp _ Sg.ι
  -- the image of `Sh` under `h` is a dense open
  let R : Set X' := Set.range (Sh.ι ≫ h)
  have hRo : IsOpen R := (Sh.ι ≫ h).isOpenEmbedding.isOpenMap.isOpen_range
  have hRd : Dense R := hdh.denseRange
  have hdres : IsDominant (h.resLE Sg S hle) := by
    have : IsDominant (h.resLE Sg S hle ≫ Sg.ι) := by
      refine ⟨(hRd.inter_of_isOpen_left hSg hRo).mono ?_⟩
      rintro x ⟨⟨y, rfl⟩, hx⟩
      refine ⟨⟨(Sh.ι y), y.2, ?_⟩, ?_⟩
      · exact hx
      · rw [Scheme.Hom.resLE_comp_ι]
        rfl
    exact IsDominant.of_comp_of_isOpenImmersion _ Sg.ι
  have hcomp : S.ι ≫ h ≫ g = h.resLE Sg S hle ≫ Sg.ι ≫ g := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι, Category.assoc]
  have hSd : Dense (S : Set Y) := by
    have h1 : Dense ((Sh.ι ≫ h) ⁻¹' (Sg : Set X')) := hSg.preimage
      (Sh.ι ≫ h).isOpenEmbedding.isOpenMap
    have h2 := (Opens.isDominant_ι hSh).denseRange.dense_image Sh.ι.continuous h1
    refine h2.mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  have : IsOpenImmersion (S.ι ≫ h ≫ g) := by rw [hcomp]; infer_instance
  exact isBirationalMorphism_of_exists (h ≫ g) S hSd (by rw [hcomp]; infer_instance)

end Birational

section Main

private lemma isOpenEmbedding_restrict_biregularLocus {Y X' : Scheme.{u}} (h : Y ⟶ X') :
    Topology.IsOpenEmbedding ((h ⁻¹ᵁ biregularLocus h : Set Y).restrict h) := by
  have : IsIso (h ∣_ biregularLocus h) := isBiregular_biregularLocus h
  have e1 := (h ∣_ biregularLocus h).isOpenEmbedding
  have e2 : Topology.IsOpenEmbedding (Subtype.val : biregularLocus h → X') :=
    (biregularLocus h).isOpen.isOpenEmbedding_subtypeVal
  have heq : (h ⁻¹ᵁ biregularLocus h : Set Y).restrict h =
      Subtype.val ∘ (h ∣_ biregularLocus h) :=
    funext fun x ↦ (morphismRestrict_base_coe h (biregularLocus h) x).symm
  rw [heq]
  exact e2.comp e1

end Main

end LogRes

/-- The klt property of the lowered boundary on a model. -/
private theorem isKltPair_of_modelInv {X Y : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {π : X ⟶ Y} {A : QDivisor Y} {hAq : A.IsQCartier} {ε : ℚ}
    (hε : 0 < ε ∧ ε < 1) {KX : Divisor X} {BX L : QDivisor X} {c0ne c0vert : Prop}
    (h : ModelInv sX π hAq ε KX BX L c0ne c0vert) (hL : MMP.Intersection.IsDltPair sX L) :
    MMP.Fourfold.IsKltPair sX L := by
  refine MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one hL fun P => ?_
  have h0 : 0 ≤ BX.coeff P := h.lc.2.1 P
  have h1 : BX.coeff P ≤ 1 := coeff_le_one_of_isLogCanonicalPair h.lc P
  rw [h.lowered]
  have : (B' : QDivisor X) → (B' - ε • Divisor.toQDivisor B'.roundDown).coeff P =
      B'.coeff P - ε * ⌊B'.coeff P⌋ := fun B' => by simp
  rw [this]
  rcases eq_or_lt_of_le h1 with h1 | h1
  · rw [h1]; simp; linarith [hε.1]
  · rw [Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩]; simpa using h1

/-- The support of a divisor is of pure codimension one. -/
private theorem isPureCodimOne_supp {X : Scheme.{0}} {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R X) : MMP.Mori.IsPureCodimOne D.supp := by
  intro W hW
  have hsub : (W : Set X) ⊆ ⋃ E ∈ D.support, E.support := fun x hx => by
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp (hW.1 hx)
    exact Set.mem_iUnion₂.mpr ⟨E, Finsupp.mem_support_iff.mpr hE, hxE⟩
  obtain ⟨E, hE, hWE⟩ := LogRes.exists_mem_of_subset_iUnion W hsub
  have hEW : LogRes.primeIrr E ≤ W := hW.2 (by
    intro x hx
    rw [LogRes.coe_primeIrr] at hx
    exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, Finsupp.mem_support_iff.mp hE, hx⟩) hWE
  rw [le_antisymm hWE hEW, LogRes.codimension_primeIrr]

/-- A closed subset equal to the support of a prime divisor is of pure codimension one. -/
private theorem isPureCodimOne_of_coe_eq_support {X : Scheme.{0}} {C : Closeds X}
    {E : MMP.Mori.PrimeDivisor X} (hC : (C : Set X) = E.support) : MMP.Mori.IsPureCodimOne C := by
  intro W hW
  have hWE : W ≤ LogRes.primeIrr E := by
    intro x hx
    change x ∈ (LogRes.primeIrr E : Set X)
    rw [LogRes.coe_primeIrr, ← hC]
    exact hW.1 hx
  have hEW : LogRes.primeIrr E ≤ W := hW.2 (by
    intro x hx
    rw [LogRes.coe_primeIrr, ← hC] at hx
    exact hx) hWE
  rw [le_antisymm hWE hEW, LogRes.codimension_primeIrr]

/-- Push-forward along a composite of proper birational morphisms of normal complex varieties is
the composite of the push-forwards. -/
private theorem transformDivisor_comp {W X X' : Scheme.{0}} [IsIntegral W] [CompactSpace W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX' : X' ⟶ Spec (.of ℂ)} (hX' : IsNormalVariety ℂ sX') (q : X ⟶ X') [IsProper q]
    (hX : IsNormalVariety ℂ (q ≫ sX')) (hqb : IsBirationalMorphism q) (r : W ⟶ X) [IsProper r]
    (hW : IsNormalVariety ℂ (r ≫ q ≫ sX')) (hrb : IsBirationalMorphism r)
    (hpb : IsBirationalMorphism (r ≫ q)) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R W) :
    RationalMap.transformDivisor (X := W) (r ≫ q).toRationalMap D =
      RationalMap.transformDivisor (X := X) q.toRationalMap
        (RationalMap.transformDivisor (X := W) r.toRationalMap D) := by
  haveI : IsSeparated sX' := hX'.1.toIsSeparated
  haveI := isSeparated_toTerminal sX'
  haveI : IsSeparated (r ≫ q ≫ sX') := hW.1.toIsSeparated
  haveI : IsSeparated ((r ≫ q) ≫ sX') := by rw [Category.assoc]; infer_instance
  haveI : IsSeparated (r ≫ q) := IsSeparated.of_comp (r ≫ q) sX'
  refine Finsupp.ext fun P => ?_
  obtain ⟨Ei, hEi, htri⟩ := exists_transformDivisor_apply hX' q hX hqb P
  obtain ⟨EW, hEW, htrW⟩ := exists_transformDivisor_apply hX r hW hrb Ei
  change _ = RationalMap.transformDivisor (X := X) q.toRationalMap _ P
  rw [htri, htrW]
  have h1 : (r ≫ q) EW.genericPoint = P.genericPoint := by
    rw [Scheme.Hom.comp_apply, hEW, hEi]
  exact MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hpb h1 D

/-- **The floor map of a divisorial step.** Let `q : X ⟶ X'` be a proper birational morphism of
`ℚ`-factorial projective surfaces over `Y` with exceptional set a prime divisor `E`, `(X, B_X)` and
`(X', q_* B_X)` models of the program whose lowered boundaries are klt, and `T`, `T'` reduced
closed subschemes on the floors. Then `q` maps `T` into `T'`, and every induced `h : T ⟶ T'`
satisfies `h_* 𝒪_T = 𝒪_{T'}` and has connected fibres.

Both claims are read off a projective log resolution `r : W ⟶ X` of `(X, B_X + E)`: `r` and
`r ≫ q` are log resolutions of `(X, B_X)` and of `(X', q_* B_X)` with the same crepant boundary
`B_W` on `W`, so the reduced floor `T_W` of `B_W` maps to `T` and to `T'` with structure-sheaf
push-forwards the structure sheaves and connected fibres
(`MMP.Fourfold.IsLogResolution.bijOn_idealSheaf_divisorialSubmodule_and_pushforward_floor`). -/
private theorem floor_map_of_divisorial {X X' Y : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sX)
    (hQ' : IsQFactorial sX') (hXp : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hX'p : MMP.Mori.IsProjectiveVariety ℂ sX') (q : X ⟶ X') [IsProper q] (hqs : q ≫ sX' = sX)
    (hqb : IsBirationalMorphism q) {E : MMP.Mori.PrimeDivisor X}
    (hE : (MMP.Mori.exceptionalSet q : Set X) = E.support) {π : X ⟶ Y} (π' : X' ⟶ Y)
    [IsDominant π'] (hqπ : q ≫ π' = π) {A : QDivisor Y} (hAq : A.IsQCartier) {ε : ℚ}
    (hε : 0 < ε ∧ ε < 1) {KX : Divisor X} {KX' : Divisor X'} {BX L : QDivisor X}
    {L' : QDivisor X'}
    {c0ne c0vert : Prop} (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hKX' : ∃ m : ℕ, KX'.IsCanonicalDivisor sX' m) (h : ModelInv sX π hAq ε KX BX L c0ne c0vert)
    (h' : ModelInv sX' π' hAq ε KX' (RationalMap.transformDivisor (X := X) q.toRationalMap BX) L'
      c0ne c0vert)
    (hLk : MMP.Fourfold.IsKltPair sX L) (hL'k : MMP.Fourfold.IsKltPair sX' L') :
    ∀ (T T' : Scheme.{0}) (ι : T ⟶ X) (ι' : T' ⟶ X')
      [IsClosedImmersion ι] [IsReduced T] [IsClosedImmersion ι'] [IsReduced T'],
      Set.range ι.base = ⋃ E ∈ BX.roundDown.support, (E.support : Set _) →
      Set.range ι'.base = ⋃ E ∈ (RationalMap.transformDivisor (X := X) q.toRationalMap
        BX).roundDown.support, (E.support : Set _) →
      (∃ h : T ⟶ T', h ≫ ι' = ι ≫ q) ∧
      ∀ h : T ⟶ T', h ≫ ι' = ι ≫ q →
        (∀ U : T'.Opens, IsIso (h.app U)) ∧ ∀ t : T', _root_.IsConnected (h.base ⁻¹' {t}) := by
  classical
  intro T T' ι ι' _ _ _ _ hTr hT'r
  subst hqs hqπ
  set B' := RationalMap.transformDivisor (X := X) q.toRationalMap BX with hB'def
  have hX' : IsNormalVariety ℂ sX' := hQ'.1
  have hX : IsNormalVariety ℂ (q ≫ sX') := hQ.1
  haveI := hqb.isDominant
  haveI : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sX') := hX.1.toLocallyOfFiniteType
  haveI := hX'.1
  haveI := hX.1
  have hdim := h.dim
  have hdim' := h'.dim
  -- the canonical divisors in dimension two
  have hKX2 := isCanonicalDivisor_two hdim hKX
  have hKX'2 := isCanonicalDivisor_two hdim' hKX'
  -- a projective log resolution of `(X, B_X + E)`
  obtain ⟨W, r, hr, hrp⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism (q ≫ sX') hX
    (QDivisor.toRDivisor BX + QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single E 1)))
  have hrs := hr.toIsSmoothResolution
  haveI : IsIntegral W := hrs.isIntegral
  haveI : IsNormal W := hrs.isNormal
  haveI : IsProper r := hrs.isProper
  have hrb := hrs.isBirationalMorphism
  haveI := hrb.isDominant
  obtain ⟨hWv, hWdim, -⟩ := hrs.isNormalVariety hX
  haveI : LocallyOfFiniteType (r ≫ q ≫ sX') := hWv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (r ≫ q ≫ sX')
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (r ≫ q ≫ sX')
  set p := r ≫ q with hpdef
  have hpb : IsBirationalMorphism p := LogRes.isBirationalMorphism_comp hrb hqb
  have hWv' : IsNormalVariety ℂ (p ≫ sX') := by rw [Category.assoc]; exact hWv
  -- `r` and `p` are log resolutions
  set Δ : RDivisor X :=
    QDivisor.toRDivisor BX + QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single E 1))
  have hΔ : ∀ P, (BX P ≠ 0 ∨ P = E) → Δ P ≠ 0 := by
    intro P hP
    have h0 : (0 : ℚ) ≤ BX P := h.lc.2.1 P
    change ((BX P : ℚ) : ℝ) + (((Finsupp.single E (1 : ℤ) : Divisor X) P : ℤ) : ℚ) ≠ 0
    rw [Finsupp.single_apply]
    rcases hP with hP | rfl
    · have : (0 : ℝ) < (BX P : ℝ) := by exact_mod_cast lt_of_le_of_ne h0 (Ne.symm hP)
      split_ifs <;> push_cast <;> linarith
    · have : (0 : ℝ) ≤ (BX P : ℝ) := by exact_mod_cast h0
      simp only [if_true]; push_cast; linarith
  have hBXΔ : (QDivisor.toRDivisor BX).supp ≤ Δ.supp := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hΔ P (Or.inl fun h0 => hP ?_), hxP⟩
    change ((BX P : ℚ) : ℝ) = 0
    rw [h0]; simp
  have hrlog : MMP.Fourfold.IsLogResolution (q ≫ sX') BX r := by
    refine ⟨⟨hrs, hr.isPureCodimOne_exceptionalSet, ?_⟩, hrp⟩
    refine LogRes.isSNCSubset_of_le hr.isSNCSubset ?_
      (sup_le_sup_left (fun x hx => hBXΔ hx) _)
    exact LogRes.isPureCodimOne_sup_preimage r.continuous (r ⁻¹ᵁ biregularLocus r).isOpen
      (LogRes.isOpenEmbedding_restrict_biregularLocus r) (fun _ hy => hy)
      hr.isPureCodimOne_exceptionalSet (isPureCodimOne_supp _)
  have hplog : MMP.Fourfold.IsLogResolution sX' B' p := by
    haveI : IsReduced X := inferInstance
    haveI : IsSeparated sX' := hX'.1.toIsSeparated
    haveI : IsSeparated (q ≫ sX') := hX.1.toIsSeparated
    haveI : IsSeparated q := IsSeparated.of_comp q sX'
    have hqp : IsProjectiveMorphism q := IsProjectiveMorphism.of_comp q sX'
      ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hXp).2
    have hEq : MMP.Mori.IsPureCodimOne (MMP.Mori.exceptionalSet q) :=
      isPureCodimOne_of_coe_eq_support hE
    have hexc := LogRes.exceptionalSet_comp r q
    -- the closed set `Ex(q) ∪ q⁻¹(Supp B')` lies in `Supp Δ`
    have hle : MMP.Mori.exceptionalSet q ⊔ (QDivisor.toRDivisor B').supp.preimage q.continuous ≤
        Δ.supp := by
      have hEx : ∀ x, x ∈ (MMP.Mori.exceptionalSet q : Set X) → x ∈ (Δ.supp : Set X) := by
        intro x hx
        have hxE : x ∈ (E.support : Set X) := by rw [← hE]; exact hx
        exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hΔ E (Or.inr rfl), hxE⟩
      intro x hx
      rcases hx with hx | hx
      · exact hEx x hx
      by_cases hxq : x ∈ (MMP.Mori.exceptionalSet q : Set X)
      · exact hEx x hxq
      obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
      obtain ⟨E₁, hE₁, htr⟩ := exists_transformDivisor_apply hX' q hX hqb P
      have hB1 : BX E₁ ≠ 0 := by
        intro h0
        apply hP
        change ((B' P : ℚ) : ℝ) = 0
        rw [hB'def, htr BX, h0]
        simp
      rw [support_eq_image_of_map_genericPoint_eq q hE₁] at hxP
      obtain ⟨z, hz, hzx⟩ := hxP
      have hxV : q x ∈ biregularLocus q := by
        simpa [MMP.Mori.mem_exceptionalSet] using hxq
      have hzV : q z ∈ biregularLocus q := by rw [hzx]; exact hxV
      have hinj := (LogRes.isOpenEmbedding_restrict_biregularLocus q).injective
        (a₁ := (⟨z, hzV⟩ : (q ⁻¹ᵁ biregularLocus q : Set X)))
        (a₂ := (⟨x, hxV⟩ : (q ⁻¹ᵁ biregularLocus q : Set X))) (by simpa [Set.restrict] using hzx)
      have hzx' : z = x := congrArg Subtype.val hinj
      exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨E₁, hΔ E₁ (Or.inl hB1), hzx' ▸ hz⟩
    refine ⟨⟨⟨inferInstance, hpb, by rw [hpdef, Category.assoc]; exact hrs.isSmoothScheme⟩, ?_, ?_⟩,
      hrp.comp hqp⟩
    · rw [hpdef, hexc]
      exact LogRes.isPureCodimOne_sup_preimage r.continuous (r ⁻¹ᵁ biregularLocus r).isOpen
        (LogRes.isOpenEmbedding_restrict_biregularLocus r) (fun _ hy => hy)
        hr.isPureCodimOne_exceptionalSet hEq
    · have heq : MMP.Mori.exceptionalSet p ⊔ (QDivisor.toRDivisor B').supp.preimage p.continuous =
          MMP.Mori.exceptionalSet r ⊔ (MMP.Mori.exceptionalSet q ⊔
            (QDivisor.toRDivisor B').supp.preimage q.continuous).preimage r.continuous := by
        rw [hpdef, hexc]
        apply SetLike.coe_injective
        ext y
        change (y ∈ MMP.Mori.exceptionalSet r ∨ r y ∈ MMP.Mori.exceptionalSet q) ∨
            (r ≫ q) y ∈ (QDivisor.toRDivisor B').supp ↔
          y ∈ MMP.Mori.exceptionalSet r ∨ (r y ∈ MMP.Mori.exceptionalSet q ∨
            q (r y) ∈ (QDivisor.toRDivisor B').supp)
        rw [Scheme.Hom.comp_apply, or_assoc]
      rw [heq, hpdef, Category.assoc]
      refine LogRes.isSNCSubset_of_le hr.isSNCSubset ?_ (sup_le_sup_left (fun x hx => hle hx) _)
      exact LogRes.isPureCodimOne_sup_preimage r.continuous (r ⁻¹ᵁ biregularLocus r).isOpen
        (LogRes.isOpenEmbedding_restrict_biregularLocus r) (fun _ hy => hy)
        hr.isPureCodimOne_exceptionalSet
        (LogRes.isPureCodimOne_sup_preimage q.continuous (q ⁻¹ᵁ biregularLocus q).isOpen
          (LogRes.isOpenEmbedding_restrict_biregularLocus q) (fun _ hy => hy) hEq
          (isPureCodimOne_supp _))
  -- a common crepant boundary on `W`
  obtain ⟨BW, hBWr, hBWp⟩ : ∃ BW : QDivisor W,
      MMP.Mori.IsCrepantBoundary (q ≫ sX') 2 KX BX r hWv hrlog.isBirationalMorphism BW ∧
        MMP.Mori.IsCrepantBoundary sX' 2 KX' B' p hWv' hplog.isBirationalMorphism BW := by
    -- a canonical divisor `K_W` of `W` and its push-forward `K'' = r_* K_W`
    have hWd : topologicalKrullDim W = ((2 : ℕ) : WithBot ℕ∞) := by rw [hWdim, hdim]; rfl
    obtain ⟨KW, hKW⟩ := @MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme W _ _ _ _ ℂ _
      (r ≫ q ≫ sX') hWv.1 hrs.isSmoothScheme 2 hWd
    obtain ⟨ωr, hωr0, hωrX, -⟩ :=
      exists_divisorOfForm_eq_transformDivisor hX hWv hrb (by rw [hdim]; rfl) hKW
    have hK''lin : (divisorOfForm ωr).LinearlyEquivalent KX := by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hKX2 hωr0 (m := 1)
    have hK''2 : (divisorOfForm ωr).IsCanonicalDivisor (q ≫ sX') 2 :=
      hKX2.of_linearlyEquivalent hK''lin
    obtain ⟨φ, hφ⟩ := hK''lin
    obtain ⟨hη, hadj⟩ := h.adj
    have hη' : ∀ Z : irreducibleComponents X', π' (componentGenericPoint X' Z) ∉ A.supp :=
      fun Z => MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' π' A Z
    have hadj'' : (Divisor.toQDivisor (divisorOfForm ωr) + BX).QLinearlyEquivalent
        (A.pullback hAq hη) := by
      refine QDivisor.QLinearlyEquivalent.trans ⟨1, one_pos, φ, ?_⟩ hadj
      rw [Nat.cast_one, one_smul, ← hφ, map_sub]
      abel
    obtain ⟨ω, hω0, hωX', -, -, hB, hpbq⟩ :=
      crepant_step hX' hQ' q hX hqb π' hAq hη hη' hK''2 hadj''
    -- the crepant boundary `B_W = r^*(K'' + B_X) - K_W`
    set N : QDivisor X := Divisor.toQDivisor (divisorOfForm ωr) + BX
    have hNq : N.IsQCartier := isQCartier_of_isQFactorial (q ≫ sX') hQ N
    have hgen : ∀ Z : irreducibleComponents W, r (componentGenericPoint W Z) ∉ N.supp :=
      fun Z => MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' r N Z
    have hNr := QDivisor.isPullback_pullback hNq hgen
    set BW := N.pullback hNq hgen - Divisor.toQDivisor KW
    have hNr' : N.IsPullback r hgen (Divisor.toQDivisor KW + BW) := by
      rw [add_sub_cancel]; exact hNr
    refine ⟨BW, ?_, ?_⟩
    · have hc := MMP.Threefold.Mori.isCrepantBoundary_of_add_eq_pullback ⟨hX, hK''2, hNq⟩ r hWv
        hrb hKW hωrX.symm ⟨hgen, hNr'⟩
      exact isCrepantBoundary_of_linearlyEquivalent hc ⟨φ, hφ⟩
    · haveI := hpb.isDominant
      obtain ⟨hM', hcomp⟩ := qDivisor_isPullback_comp q r hpbq hNr'
      have hpush : RationalMap.transformDivisor (X := W) p.toRationalMap KW = divisorOfForm ω := by
        rw [hpdef, transformDivisor_comp hX' q hX hqb r hWv hrb hpb, ← hωrX, hωX']
      have hωK : (divisorOfForm ω).LinearlyEquivalent KX' := by
        simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX' hKX'2 hω0 (m := 1)
      have hKω : (divisorOfForm ω).IsCanonicalDivisor sX' 2 := hKX'2.of_linearlyEquivalent hωK
      have hNq' := isQCartier_of_isQFactorial sX' hQ' (Divisor.toQDivisor (divisorOfForm ω) + B')
      have hKW' : KW.IsCanonicalDivisor (p ≫ sX') 2 := by
        rw [hpdef, Category.assoc]; exact hKW
      have hc := MMP.Threefold.Mori.isCrepantBoundary_of_add_eq_pullback ⟨hX', hKω, hNq'⟩ p hWv'
        hpb hKW' hpush ⟨hM', hcomp⟩
      exact isCrepantBoundary_of_linearlyEquivalent hc hωK
  -- the floor of `B_W`
  have hBW1 : ∀ F, BW.coeff F ≤ 1 := by
    intro F
    have h0 := h.lc.2.2 2 _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy
      (hBWr F) (show IsProper r from inferInstance))
    have : ((BW.coeff F : ℚ) : ℝ) ≤ 1 := by push_cast at h0; linarith
    exact_mod_cast this
  set TW : Divisor W := ∑ F ∈ BW.support.filter (fun F => BW.coeff F = 1), Finsupp.single F 1
    with hTWdef
  have hTW : ∀ F, TW.coeff F = if BW.coeff F = 1 then 1 else 0 := by
    intro F
    change (∑ F' ∈ BW.support.filter (fun F => BW.coeff F = 1), Finsupp.single F' (1 : ℤ)) F = _
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    by_cases h1 : BW.coeff F = 1
    · have hm : F ∈ BW.support.filter (fun F => BW.coeff F = 1) :=
        Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by
          rw [show BW F = BW.coeff F from rfl, h1]; exact one_ne_zero), h1⟩
      rw [if_pos hm, if_pos h1]
    · have hm : F ∉ BW.support.filter (fun F => BW.coeff F = 1) :=
        fun hm => h1 (Finset.mem_filter.mp hm).2
      rw [if_neg hm, if_neg h1]
  have hΓ : ∀ F, (BW - Divisor.toQDivisor TW).coeff F < 1 := by
    intro F
    rw [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, hTW]
    by_cases h1 : BW.coeff F = 1
    · rw [if_pos h1, h1]; norm_num
    · rw [if_neg h1]
      simpa using lt_of_le_of_ne (hBW1 F) h1
  set ZW : Closeds W := ⟨⋃ F ∈ TW.support, (F.support : Set W),
    TW.support.finite_toSet.isClosed_biUnion fun F _ => F.idealSheaf.support.isClosed⟩
  set ιT := (Scheme.IdealSheafData.vanishingIdeal ZW).subschemeι
  have hTWr : Set.range ιT.base = ⋃ F ∈ TW.support, (F.support : Set W) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  -- the two floor maps from `T_W`
  have hB : MMP.Intersection.IsLogCanonicalPair (q ≫ sX') BX ∧ ∃ δ : ℚ, 0 < δ ∧
      MMP.Fourfold.IsKltPair (q ≫ sX') (BX - δ • Divisor.toQDivisor BX.roundDown) :=
    ⟨h.lc, ε, hε.1, by rw [← h.lowered]; exact hLk⟩
  have hB' : MMP.Intersection.IsLogCanonicalPair sX' B' ∧ ∃ δ : ℚ, 0 < δ ∧
      MMP.Fourfold.IsKltPair sX' (B' - δ • Divisor.toQDivisor B'.roundDown) :=
    ⟨h'.lc, ε, hε.1, by rw [← h'.lowered]; exact hL'k⟩
  obtain ⟨-, -, ⟨a, ha⟩, ha'⟩ :=
    MMP.Fourfold.IsLogResolution.bijOn_idealSheaf_divisorialSubmodule_and_pushforward_floor
      hdim hKX2 hXp hQ (Or.inr hB) hrlog ⟨hWv, hBWr⟩ hTW hΓ ι ιT hTr hTWr
  obtain ⟨-, -, ⟨b, hb⟩, hb'⟩ :=
    MMP.Fourfold.IsLogResolution.bijOn_idealSheaf_divisorialSubmodule_and_pushforward_floor
      hdim' hKX'2 hX'p hQ' (Or.inr hB') hplog ⟨hWv', hBWp⟩ hTW hΓ ι' ιT hT'r hTWr
  obtain ⟨haiso, -, hasurj, -⟩ := ha' a ha
  -- the floor of `X` maps into the floor of `X'`
  have hsub : Set.range (ι ≫ q).base ⊆ Set.range ι'.base := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨w, rfl⟩ := hasurj x
    have heq : b ≫ ι' = a ≫ ι ≫ q := by
      rw [hb, hpdef, ← Category.assoc, ← ha, Category.assoc]
    refine ⟨b.base w, ?_⟩
    have := congrArg (fun φ : (Scheme.IdealSheafData.vanishingIdeal ZW).subscheme ⟶ X' => φ.base w)
      heq
    simpa using this
  have hker : ι'.ker ≤ (ι ≫ q).ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range (ι ≫ q),
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    change closure (Set.range (ι ≫ q).base) ⊆ (ι'.ker.support : Set X')
    rw [Scheme.Hom.support_ker, ι'.isClosedEmbedding.isClosed_range.closure_eq]
    exact closure_minimal hsub ι'.isClosedEmbedding.isClosed_range
  refine ⟨⟨IsClosedImmersion.lift ι' (ι ≫ q) hker, IsClosedImmersion.lift_fac _ _ _⟩,
    fun f hf => ?_⟩
  have hg : (a ≫ f) ≫ ι' = ιT ≫ p := by
    rw [Category.assoc, hf, ← Category.assoc, ha, Category.assoc]
  obtain ⟨hgiso, -, -, hgconn⟩ := hb' (a ≫ f) hg
  refine ⟨fun U => ?_, fun t => ?_⟩
  · have h1 := hgiso U
    rw [Scheme.Hom.comp_app] at h1
    haveI := haiso (f ⁻¹ᵁ U)
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (f.app U) (a.app (f ⁻¹ᵁ U)) _ h1
  · have heq : f.base ⁻¹' {t} = a.base '' ((a ≫ f).base ⁻¹' {t}) := by
      ext x
      constructor
      · intro hx
        obtain ⟨w, rfl⟩ := hasurj x
        exact ⟨w, by rw [Set.mem_preimage, Scheme.Hom.comp_apply]; exact hx, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]; exact hw
    rw [heq]
    exact (hgconn t).image _ a.base.hom.continuous.continuousOn

/-- **One step of the program.** -/
private theorem step {S Y : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S]
    [IsNormal S] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sS : S ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {p : S ⟶ Y} {K : Divisor S}
    {B : QDivisor S} {A : QDivisor Y} (hAq : A.IsQCartier) {ε : ℚ} (hε : 0 < ε ∧ ε < 1)
    {c0ne c0vert : Prop}
    (P : RelativeDltProgram sS sY p K (B - ε • Divisor.toQDivisor B.roundDown))
    (hP : P.IsProjective) (i : ℕ) (hi : (i : ℕ∞) < P.n)
    (h : ModelInv (modelStr sS P.sY i) (modelMap p P.πY i) hAq ε (divisorSeq K P.KY i)
      (iterTransform P.φ B i) (divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY i)
      c0ne c0vert) :
    (IsBirationalMorphism (P.f i) ∧
      (∃ E : MMP.Mori.PrimeDivisor (modelSeq S P.Y i),
        (MMP.Mori.exceptionalSet (P.f i) : Set (modelSeq S P.Y i)) = E.support) ∧
      IsIso (P.fp i) ∧
      ∃ q : modelSeq S P.Y i ⟶ P.Y i, q ≫ P.fp i = P.f i ∧
        (∃ (hqY : IsNormalVariety ℂ (q ≫ P.sY i)) (hq : IsBirationalMorphism q),
          MMP.Mori.IsCrepantBoundary (P.sY i) 2 (P.KY i) (iterTransform P.φ B (i + 1)) q hqY hq
            (iterTransform P.φ B i)) ∧
        ∀ (T T' : Scheme.{0}) (ι : T ⟶ modelSeq S P.Y i) (ι' : T' ⟶ P.Y i)
          [IsClosedImmersion ι] [IsReduced T] [IsClosedImmersion ι'] [IsReduced T'],
          Set.range ι.base =
              ⋃ E ∈ (iterTransform P.φ B i).roundDown.support, (E.support : Set _) →
          Set.range ι'.base =
              ⋃ E ∈ (iterTransform P.φ B (i + 1)).roundDown.support, (E.support : Set _) →
          (∃ h : T ⟶ T', h ≫ ι' = ι ≫ q) ∧
          ∀ h : T ⟶ T', h ≫ ι' = ι ≫ q →
            (∀ U : T'.Opens, IsIso (h.app U)) ∧ ∀ t : T', _root_.IsConnected (h.base ⁻¹' {t})) ∧
    ModelInv (modelStr sS P.sY (i + 1)) (modelMap p P.πY (i + 1)) hAq ε
      (divisorSeq K P.KY (i + 1)) (iterTransform P.φ B (i + 1))
      (divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY (i + 1)) c0ne c0vert := by
  classical
  have hstep := P.isElementaryDltStep i hi
  have hmi := P.isRelativeDltModel i hi.le
  have hi1 : ((i + 1 : ℕ) : ℕ∞) ≤ P.n := by
    have := Order.add_one_le_of_lt hi
    exact_mod_cast this
  have hmi1 := P.isRelativeDltModel (i + 1) hi1
  have hctr := hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction
  obtain ⟨hfb, hexc, hiso, hmod⟩ : IsBirationalMorphism (P.f i) ∧
      (∃ E : MMP.Mori.PrimeDivisor (modelSeq S P.Y i),
        (MMP.Mori.exceptionalSet (P.f i) : Set (modelSeq S P.Y i)) = E.support) ∧
      IsIso (P.fp i) ∧ IsModificationOf (P.f i) (P.fp i) (P.φ i) := by
    rcases hstep.divisorial_or_flip with h' | hflip
    · exact h'
    · exact (false_of_isSmall_of_isNegativeExtremalContraction h.dim hflip.isSmall_source
        hctr).elim
  haveI := hiso
  set q : modelSeq S P.Y i ⟶ P.Y i := P.f i ≫ inv (P.fp i) with hqdef
  have hq : q ≫ P.fp i = P.f i := by simp [q]
  have hφ : P.φ i = q.toRationalMap := eq_toRationalMap_of_isOver _ _ _ hmod.2
  have hfg := hstep.isNegativeRelativeRayContraction.isRelativeContractionOfFace.comp_eq
  have hfpg := hstep.comp_eq
  have hqπ : q ≫ P.πY i = modelMap p P.πY i := by
    rw [← hfpg, ← Category.assoc, hq, hfg]
  have hqs : q ≫ P.sY i = modelStr sS P.sY i := by
    have h1 := hmi1.comp_eq
    have h0 := hmi.comp_eq
    change P.πY i ≫ sY = P.sY i at h1
    rw [← h1, ← Category.assoc, hqπ, h0]
  have hZ : IsNormalVariety ℂ (P.sZ i) := hctr.isNormalVariety_target
  haveI : IsIntegral (P.Z i) := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
  haveI : IsNormal (P.Z i) := hZ.2
  haveI : IsProper (P.f i) := hctr.isContraction.isProper
  haveI : IsProper q := by rw [hqdef]; infer_instance
  have hqb : IsBirationalMorphism q :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational (inv (P.fp i)) (P.f i)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
        (isBirationalMorphism_of_isIso _))
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
  haveI : IsDominant (modelMap p P.πY i) := h.dom
  haveI : IsDominant (q ≫ P.πY i) := by rw [hqπ]; infer_instance
  haveI : IsDominant (P.πY i) := IsDominant.of_comp q (P.πY i)
  have hQ' : IsQFactorial (P.sY i) := hmi1.isQFactorial
  have hKX := hmi.isCanonicalDivisor
  have hKX' : ∃ m : ℕ, (P.KY i).IsCanonicalDivisor (P.sY i) m := hmi1.isCanonicalDivisor
  have hL' : P.BY i = RationalMap.transformDivisor (X := modelSeq S P.Y i) q.toRationalMap
      (divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY i) := by
    rw [P.BY_eq i hi, hφ]
  have hBU : iterTransform P.φ B (i + 1) =
      RationalMap.transformDivisor (X := modelSeq S P.Y i) q.toRationalMap
        (iterTransform P.φ B i) := by
    change RationalMap.transformDivisor (P.φ i) _ = _
    rw [hφ]
  have hXv : MMP.Mori.IsVariety ℂ (modelStr sS P.sY i) := hmi.isQFactorial.1.1
  haveI : QuasiCompact (modelStr sS P.sY i) := hXv.toQuasiCompact
  have hYv : MMP.Mori.IsVariety ℂ sY := hP.1.1
  have hπ' : P.πY i ≫ sY = P.sY i := hmi1.comp_eq
  obtain ⟨E, hE⟩ := hexc
  have hexcq : (MMP.Mori.exceptionalSet q : Set (modelSeq S P.Y i)) = E.support := by
    rw [← hE]
    have h1 := (MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq ℂ hXv
      hQ'.1.1 q hqs (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hqb)).2.1
    have h2 := (MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq ℂ hXv
      hZ.1 (P.f i) hctr.isContraction.comp_eq
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)).2.1
    rw [h1, h2]
    ext u
    have hfib : ∀ x, q x = q u ↔ P.f i x = P.f i u := fun x => by
      rw [← hq]
      simp only [Scheme.Hom.comp_apply]
      exact ⟨fun h' => by rw [h'], fun h' =>
        (ConcreteCategory.bijective_of_isIso (P.fp i).base).1 h'⟩
    have : (q ⁻¹' {q u} : Set _) = P.f i ⁻¹' {P.f i u} := by
      ext x; exact hfib x
    simp only [Set.mem_setOf_eq]
    rw [this]
  have hneg : ∀ C : ProperCurve (modelStr sS P.sY i), C.IsContractedBy q →
      ∀ hD : (Divisor.toQDivisor (divisorSeq K P.KY i) +
        divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY i).IsQCartier,
      (Divisor.toQDivisor (divisorSeq K P.KY i) +
        divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY i).intersectionNumber ℂ
          (modelStr sS P.sY i) C.ι C.dim_le hD < 0 := by
    intro C hC hD
    refine intersectionNumber_neg_of_isRelativelyAntiAmple (P.f i) hD
      hctr.isRelativelyAntiAmple C fun x hx => ?_
    rw [← hq]
    simp only [Scheme.Hom.comp_apply]
    rw [hC x hx]
  obtain ⟨hcrep, hinv'⟩ := divisorial_step hQ' q hqs hqb (P.πY i) hqπ hAq hKX hKX' h
    (fun hc => roundDown_transformDivisor_ne_zero hQ' hmi.isQFactorial (hP.2 i hi.le) hYv q hqs
      hqb (P.πY i) hπ' hqπ hAq hε h hexcq hneg (h.ne hc))
  have hinv1 : ModelInv (modelStr sS P.sY (i + 1)) (modelMap p P.πY (i + 1)) hAq ε
      (divisorSeq K P.KY (i + 1)) (iterTransform P.φ B (i + 1))
      (divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY (i + 1)) c0ne c0vert := by
    change ModelInv (P.sY i) (P.πY i) hAq ε (P.KY i) (iterTransform P.φ B (i + 1)) (P.BY i)
      c0ne c0vert
    rw [hBU, hL']
    exact hinv'
  refine ⟨⟨hfb, ⟨E, hE⟩, hiso, q, hq, ⟨?_, hqb, ?_⟩, ?_⟩, hinv1⟩
  · rw [hqs]; exact hmi.isQFactorial.1
  · rw [hBU]; exact hcrep _ _
  · rw [hBU]
    exact floor_map_of_divisorial hmi.isQFactorial hQ' (hP.2 i hi.le) (hP.2 (i + 1) hi1) q hqs
      hqb hexcq (P.πY i) hqπ hAq hε hKX hKX' h hinv' (isKltPair_of_modelInv hε h hmi.isDltPair)
      (isKltPair_of_modelInv hε hinv' (by rw [← hL']; exact hmi1.isDltPair))

/-! ### Curves in the fibres over a curve -/

section FibreCurves

/-- In `WithBot ℕ∞`, `a < 2` gives `a ≤ 1`. -/
private theorem le_one_of_lt_two {a : WithBot ℕ∞} (h : a < 2) : a ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe n =>
    have : n < 2 := WithBot.coe_lt_coe.mp h
    have : n ≤ 1 := Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using this)
    exact WithBot.coe_le_coe.mpr this

/-- On an integral scheme of dimension at most one, every point is closed or generic. -/
private theorem isClosed_or_eq_genericPoint {T : Scheme.{0}} [IsIntegral T]
    (hT : topologicalKrullDim T ≤ 1) (z : T) :
    IsClosed ({z} : Set T) ∨ z = genericPoint T := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hzc, hzg⟩ := hcon
  obtain ⟨w, hw, hwz⟩ : ∃ w ∈ closure ({z} : Set T), w ≠ z := by
    by_contra h'
    push Not at h'
    apply hzc
    have : closure ({z} : Set T) = {z} :=
      Set.Subset.antisymm (fun w hw => h' w hw) subset_closure
    rw [← this]; exact isClosed_closure
  have hsp : z ⤳ w := specializes_iff_mem_closure.mpr hw
  have hlt : w < z := lt_of_le_not_ge hsp fun h => hwz (Specializes.antisymm h hsp).eq
  have hg : genericPoint T ⤳ z := (genericPoint_spec T).specializes trivial
  have hlt' : z < genericPoint T :=
    lt_of_le_not_ge hg fun h => hzg (Specializes.antisymm h hg).eq
  have h1 := coheight_le_of_topologicalKrullDim_le hT (genericPoint T)
  have h2 := Order.coheight_strictAnti hlt' (lt_of_le_of_lt h1 (by decide))
  have h3 := Order.coheight_strictAnti hlt (lt_of_le_of_lt
    (coheight_le_of_topologicalKrullDim_le hT z) (by decide))
  have h4 := coheight_le_of_topologicalKrullDim_le hT w
  have : (1 : ℕ∞) < Order.coheight w :=
    lt_of_le_of_lt (le_trans (by simp) (Order.add_one_le_of_lt h2)) h3
  exact absurd (lt_of_lt_of_le this h4) (lt_irrefl _)

/-- A normal complex curve is smooth. -/
private theorem isSmoothScheme_of_topologicalKrullDim_eq_one {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hYv : MMP.Mori.IsVariety ℂ sY)
    (hY : topologicalKrullDim Y = 1) : IsSmoothScheme sY := by
  have hcl : ∀ y : Y, y ≠ genericPoint Y → y ∈ smoothLocus sY := fun y hy => by
    set Qy : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y
      (coheight_eq_one_of_ne_genericPoint hY hy)
    have hQy : Qy.genericPoint = y :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    have := MMP.Threefold.Mori.CanonUniq.genericPoint_mem_smoothLocus (f := sY) hYv Qy
    rwa [hQy] at this
  have hne : ∃ y₀ : Y, y₀ ≠ genericPoint Y := by
    by_contra hcon
    push Not at hcon
    apply not_isClosed_genericPoint hY
    convert (isClosed_univ : IsClosed (Set.univ : Set Y)) using 1
    ext y; simp [hcon y]
  obtain ⟨y₀, hy₀⟩ := hne
  refine eq_top_iff.mpr fun y _ => ?_
  by_cases hy : y = genericPoint Y
  · rw [hy]
    exact ((genericPoint_spec Y).specializes trivial : genericPoint Y ⤳ y₀).mem_open
      (smoothLocus sY).isOpen (hcl y₀ hy₀)
  · exact hcl y hy

/-- Every point of `X` over a closed point `y ≠ η_Y` of a normal curve `Y` lies on a prime
divisor of `X` lying over `y`: the fibre is the support of the fibre divisor `π^*y`. -/
private theorem exists_primeDivisor_mem_support_of_map_eq {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hYv : MMP.Mori.IsVariety ℂ sY)
    (hY : topologicalKrullDim Y = 1) (π : X ⟶ Y) [IsDominant π] {y : Y}
    (hyc : IsClosed ({y} : Set Y)) (hyg : y ≠ genericPoint Y) {x : X} (hx : π x = y) :
    ∃ E : MMP.Mori.PrimeDivisor X, x ∈ E.support ∧ π E.genericPoint = y := by
  have hcart : ∀ D : Divisor Y, D.IsCartier :=
    isCartier_of_isSmoothScheme (isSmoothScheme_of_topologicalKrullDim_eq_one hYv hY)
  have hgen : ∀ (D : Divisor Y) (Z : irreducibleComponents X),
      π (componentGenericPoint X Z) ∉ D.supp := fun D Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' π D Z
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y
    (coheight_eq_one_of_ne_genericPoint hY hyg)
  have hP : MMP.Mori.PrimeDivisor.genericPoint P = y :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hPc : IsClosed ({MMP.Mori.PrimeDivisor.genericPoint P} : Set Y) := by rw [hP]; exact hyc
  set F := Divisor.pullback (f := π) (Finsupp.single P 1 : Divisor Y) (hcart _) (hgen _)
  have hF : Divisor.IsPullback π (Finsupp.single P 1 : Divisor Y) (hgen _) F :=
    Divisor.isPullback_pullback (hcart _) (hgen _)
  have hxF : x ∈ F.supp := mem_supp_of_isPullback_single π P hF (by rw [hx, hP])
  obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxF
  refine ⟨E, hxE, ?_⟩
  by_contra hne
  exact hE (coeff_eq_zero_of_isPullback_single π P hPc hF E (by rw [hP]; exact hne))

/-- A prime divisor lying over a closed point lies in its fibre. -/
private theorem map_eq_of_mem_support {X Y : Scheme.{0}} (π : X ⟶ Y)
    {E : MMP.Mori.PrimeDivisor X} (hc : IsClosed ({π E.genericPoint} : Set Y)) {x : X}
    (hx : x ∈ E.support) : π x = π E.genericPoint := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
  have h1 := (specializes_iff_mem_closure.mpr hx).map π.base.hom.continuous
  have h2 := specializes_iff_mem_closure.mp h1
  rwa [hc.closure_eq] at h2

/-- A component of a vertical divisor lies over a closed point. -/
private theorem isClosed_map_genericPoint_of_isVertical {X Y : Scheme.{0}} (π : X ⟶ Y)
    [UniversallyClosed π] {D : QDivisor X} (hv : QDivisor.IsVertical π D)
    {E : MMP.Mori.PrimeDivisor X} (hE : D E ≠ 0) : IsClosed ({π E.genericPoint} : Set Y) := by
  have himg : π.base '' E.support = {π E.genericPoint} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨E.genericPoint, ?_, rfl⟩, ?_⟩
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    · rintro _ ⟨z, hz, rfl⟩; exact hv E hE z hz
  rw [← himg]
  exact π.isClosedMap _ E.idealSheaf.support.isClosed

/-- The floor components which are vertical over `Y` lie over finitely many closed points: there
is a closed point `y` of the curve `Y`, other than its generic point, over which no vertical floor
component lies. -/
private theorem exists_closed_notMem_image {X Y : Scheme.{0}} [IsIntegral Y]
    {sY : Y ⟶ Spec (.of ℂ)} (hYv : MMP.Mori.IsVariety ℂ sY) (hY : topologicalKrullDim Y = 1)
    (π : X ⟶ Y) (S : Finset (MMP.Mori.PrimeDivisor X))
    (hS : ∀ E ∈ S, IsClosed ({π E.genericPoint} : Set Y)) :
    ∃ y : Y, IsClosed ({y} : Set Y) ∧ y ≠ genericPoint Y ∧ ∀ E ∈ S, π E.genericPoint ≠ y := by
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  set W : Set Y := ⋃ E ∈ S, {π E.genericPoint}
  have hW : IsClosed W := S.finite_toSet.isClosed_biUnion fun E hE => hS E hE
  have hgW : genericPoint Y ∉ W := by
    intro h
    obtain ⟨E, hE, h'⟩ := Set.mem_iUnion₂.mp h
    rw [Set.mem_singleton_iff] at h'
    exact not_isClosed_genericPoint hY (h' ▸ hS E hE)
  obtain ⟨y, hyW, hyc⟩ := nonempty_inter_closedPoints (Z := Wᶜ) ⟨_, hgW⟩
    hW.isOpen_compl.isLocallyClosed
  refine ⟨y, hyc, fun h => not_isClosed_genericPoint hY (h ▸ hyc), fun E hE h => hyW ?_⟩
  exact Set.mem_iUnion₂.mpr ⟨E, hE, h ▸ rfl⟩

end FibreCurves

/-- **The lowered adjoint is not nef over `Y` when the floor is horizontal, or when `Y` is a
point and the floor is nonzero.** A curve `F` contracted over `Y`, meeting the floor and not
contained in it, has `(K + B)·F = 0` and `⌊B⌋·F > 0`, so `(K + B - ε⌊B⌋)·F < 0`. -/
private theorem not_isRelativelyNef_of_not_isVertical {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX) {π : X ⟶ Y}
    (hπ : π ≫ sY = sX) (hπp : IsProjectiveMorphism π) (hYp : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hY : topologicalKrullDim Y ≤ 1) {A : QDivisor Y} (hAq : A.IsQCartier) {ε : ℚ}
    (hε : 0 < ε ∧ ε < 1) {KX : Divisor X} {BX L : QDivisor X} {c0ne c0vert : Prop}
    (h : ModelInv sX π hAq ε KX BX L c0ne c0vert)
    (hcase : ¬ QDivisor.IsVertical π (Divisor.toQDivisor BX.roundDown) ∨
      (topologicalKrullDim Y = 0 ∧ BX.roundDown ≠ 0)) :
    ¬ IsRelativelyNef ℂ sX π (QDivisor.toRDivisor (Divisor.toQDivisor KX + L)) := by
  classical
  intro hnef
  haveI : IsDominant π := h.dom
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  haveI : IsProper sX := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp
    ((MMP.Mori.isProjectiveVariety_iff ℂ sX).mp hX).2).2
  haveI : IsProper π := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hπp).2
  have hYv : MMP.Mori.IsVariety ℂ sY := hYp.1
  set A : QDivisor X := Divisor.toQDivisor BX.roundDown with hAdef
  have hA0 : 0 ≤ A := fun E => by
    change (0 : ℚ) ≤ ((BX.roundDown E : ℤ) : ℚ)
    have : (0 : ℚ) ≤ BX E := h.lc.2.1 E
    exact_mod_cast Int.floor_nonneg.mpr this
  have hqf := fun D : QDivisor X => isQCartier_of_isQFactorial sX hQ D
  have hmemA : ∀ E, E ∈ BX.roundDown.support ↔ A E ≠ 0 := fun E => by
    rw [Finsupp.mem_support_iff]
    change _ ↔ ((BX.roundDown E : ℤ) : ℚ) ≠ 0
    exact_mod_cast Iff.rfl
  -- a curve contracted by `π` on which the floor is positive
  obtain ⟨C, hCπ, hpos⟩ : ∃ C : ProperCurve sX, C.IsContractedBy π ∧
      ∃ hC : C.point ∉ A.supp, ∃ p : X, C.point ⤳ p ∧ p ∈ A.supp := by
    rcases hcase with hhor | ⟨hY0, hne⟩
    · -- a horizontal floor component `E₀`
      obtain ⟨E₀, hAE₀, x₀, hx₀, hx₀ne⟩ : ∃ E₀ : MMP.Mori.PrimeDivisor X, A E₀ ≠ 0 ∧
          ∃ x₀ ∈ E₀.support, π x₀ ≠ π E₀.genericPoint := by
        by_contra hcon
        push Not at hcon
        exact hhor hcon
      have hE₀nc : ¬ IsClosed ({π E₀.genericPoint} : Set Y) := fun hc =>
        hx₀ne (map_eq_of_mem_support π hc hx₀)
      have hE₀g : π E₀.genericPoint = genericPoint Y :=
        (isClosed_or_eq_genericPoint hY _).resolve_left hE₀nc
      have hY1 : topologicalKrullDim Y = 1 := by
        refine le_antisymm hY (one_le_topologicalKrullDim_of_specializes_of_ne
          ((specializes_iff_mem_closure.mpr ?_).map π.base.hom.continuous) (Ne.symm hx₀ne))
        rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      -- the vertical floor components
      set S := BX.roundDown.support.filter fun E => IsClosed ({π E.genericPoint} : Set Y)
      obtain ⟨y, hyc, hyg, hyS⟩ := exists_closed_notMem_image hYv hY1 π S
        fun E hE => (Finset.mem_filter.mp hE).2
      -- a closed point of `E₀` over `y`
      have himg : π.base '' E₀.support = Set.univ := by
        refine Set.eq_univ_of_forall fun z => ?_
        have hcl : IsClosed (π.base '' E₀.support) :=
          π.isClosedMap _ E₀.idealSheaf.support.isClosed
        have hz : genericPoint Y ⤳ z := (genericPoint_spec Y).specializes trivial
        refine hz.mem_closed hcl ⟨E₀.genericPoint, ?_, hE₀g⟩
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      have hy₁ : y ∈ π.base '' E₀.support := himg ▸ Set.mem_univ y
      obtain ⟨p₁, hp₁, hp₁y⟩ := hy₁
      have hZc : IsClosed ((E₀.support : Set X) ∩ π.base ⁻¹' {y}) :=
        E₀.idealSheaf.support.isClosed.inter (hyc.preimage π.base.hom.continuous)
      obtain ⟨p, ⟨hpE₀, hpy⟩, hpc⟩ := nonempty_inter_closedPoints
        (Z := (E₀.support : Set X) ∩ π.base ⁻¹' {y}) ⟨p₁, hp₁, hp₁y⟩ hZc.isLocallyClosed
      obtain ⟨E, hpE, hEy⟩ := exists_primeDivisor_mem_support_of_map_eq hYv hY1 π hyc hyg hpy
      have hEc : IsClosed ({π E.genericPoint} : Set Y) := by rw [hEy]; exact hyc
      have hAE : A E = 0 := by
        by_contra hAE
        exact hyS E (Finset.mem_filter.mpr ⟨(hmemA E).mpr hAE, hEc⟩) hEy
      refine ⟨⟨E.genericPoint, isProperCurve_genericPoint sX h.dim E⟩, fun z hz =>
        map_eq_of_mem_support π hEc (by rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure]),
        fun hEA => ?_, p, ?_, DivisorWithCoeffs.mem_supp_iff.mpr ⟨E₀, hAE₀, hpE₀⟩⟩
      · obtain ⟨E', hE', hEE'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hEA
        have := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E hEE'
        subst this
        exact hE' hAE
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hpE
        exact specializes_iff_mem_closure.mpr hpE
    · -- `Y` is a point
      obtain ⟨E₀, hE₀⟩ := Finsupp.ne_iff.mp hne
      have hAE₀ : A E₀ ≠ 0 := (hmemA E₀).mp (Finsupp.mem_support_iff.mpr hE₀)
      have hηE₀ : E₀.genericPoint ∈ (E₀.support : Set X) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      obtain ⟨p, hpE₀, hpc⟩ := nonempty_inter_closedPoints (X := X) ⟨_, hηE₀⟩
        E₀.idealSheaf.support.isClosed.isLocallyClosed
      have hpA : p ∈ A.supp := DivisorWithCoeffs.mem_supp_iff.mpr ⟨E₀, hAE₀, hpE₀⟩
      obtain ⟨y', -, hy'p, hy'A, hy'⟩ := exists_isProperCurve_of_specializes sX
        ((genericPoint_spec X).specializes trivial : genericPoint X ⤳ p) hpc
        (DivisorWithCoeffs.isClosed_supp A) hpA (genericPoint_notMem_supp A)
      have hYpt : ∀ z : Y, z = genericPoint Y := fun z => by
        by_contra hz
        have := one_le_topologicalKrullDim_of_specializes_of_ne
          ((genericPoint_spec Y).specializes trivial : genericPoint Y ⤳ z) (Ne.symm hz)
        rw [hY0] at this
        exact absurd this (by decide)
      exact ⟨⟨y', hy'⟩, fun z _ => (hYpt _).trans (hYpt _).symm, hy'A, p, hy'p, hpA⟩
  obtain ⟨hCA, p, hCp, hpA⟩ := hpos
  have hApos : 0 < A.intersectionNumber ℂ sX C.ι C.dim_le (hqf A) := by
    obtain ⟨h1, h2⟩ := intersectionNumber_nonneg_and_eq_zero_iff sX A (hqf A) hA0 C hCA
    exact lt_of_le_of_ne h1 fun h0 => (h2.mp h0.symm) p hCp hpA
  have h1 := intersectionNumber_nonneg_of_isRelativelyNef π (hqf _) hnef C hCπ
  rw [h.intersectionNumber_eq hQ hYv hπ C hCπ] at h1
  nlinarith [hε.1]

/-- **No Mori fibre space over a curve when the floor is vertical.** A fibre `F` of the final
contraction `g` over a point of `T` outside the image of the floor is disjoint from the floor,
so `(K + B - ε⌊B⌋)·F = (K + B)·F = 0`, against the negativity of the final ray. -/
private theorem false_of_isNegativeRelativeRayContraction_of_isVertical {X Y T : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX) {π : X ⟶ Y}
    (hπ : π ≫ sY = sX) (hπp : IsProjectiveMorphism π) (hYp : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hY : topologicalKrullDim Y = 1) {A : QDivisor Y} (hAq : A.IsQCartier) {ε : ℚ}
    (hε : 0 < ε ∧ ε < 1) {KX : Divisor X} {BX L : QDivisor X} {c0ne c0vert : Prop}
    (h : ModelInv sX π hAq ε KX BX L c0ne c0vert)
    (hv : QDivisor.IsVertical π (Divisor.toQDivisor BX.roundDown))
    {R : Set (RelativeNumericalCurveClasses sX π)} {g : X ⟶ T} {gT : T ⟶ Y}
    (hg : IsNegativeRelativeRayContraction sX π sT (Divisor.toQDivisor KX + L) R g gT)
    (hdim : topologicalKrullDim T < topologicalKrullDim X) : False := by
  classical
  haveI : IsDominant π := h.dom
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : IsProper sX := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp
    ((MMP.Mori.isProjectiveVariety_iff ℂ sX).mp hX).2).2
  haveI : IsProper π := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hπp).2
  have hYv : MMP.Mori.IsVariety ℂ sY := hYp.1
  have hT := hg.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral T := hT.1.toIsIntegral
  have hTdim : topologicalKrullDim T ≤ 1 := by
    rw [h.dim] at hdim
    exact le_one_of_lt_two hdim
  have hgT : g ≫ gT = π := hg.isRelativeContractionOfFace.comp_eq
  set A : QDivisor X := Divisor.toQDivisor BX.roundDown
  have hqf := fun D : QDivisor X => isQCartier_of_isQFactorial sX hQ D
  -- the floor components lie over closed points
  have hAc : ∀ E ∈ BX.roundDown.support, IsClosed ({π E.genericPoint} : Set Y) := by
    intro E hE
    have hAE : A E ≠ 0 := by
      change ((BX.roundDown E : ℤ) : ℚ) ≠ 0
      exact_mod_cast Finsupp.mem_support_iff.mp hE
    exact isClosed_map_genericPoint_of_isVertical π hv hAE
  obtain ⟨y, hyc, hyg, hyS⟩ := exists_closed_notMem_image hYv hY π _ hAc
  obtain ⟨x, hx⟩ := π.surjective y
  obtain ⟨E, -, hEy⟩ := exists_primeDivisor_mem_support_of_map_eq hYv hY π hyc hyg hx
  let C : ProperCurve sX := ⟨E.genericPoint, isProperCurve_genericPoint sX h.dim E⟩
  have hCE : closure ({C.point} : Set X) = E.support :=
    (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have hEc : IsClosed ({π E.genericPoint} : Set Y) := by rw [hEy]; exact hyc
  have hCπ : C.IsContractedBy π := fun z hz =>
    map_eq_of_mem_support π hEc (hCE ▸ hz)
  -- the curve is contracted by `g`
  have hCg : C.IsContractedBy g := by
    rcases isClosed_or_eq_genericPoint hTdim (g E.genericPoint) with hc | hgen
    · exact fun z hz => map_eq_of_mem_support g hc (hCE ▸ hz)
    · exfalso
      have hall : ∀ z : X, π z = y := fun z => by
        have h1 : genericPoint T ⤳ g z := (genericPoint_spec T).specializes trivial
        have h2 := h1.map gT.base.hom.continuous
        have h3 : gT (genericPoint T) = y := by
          rw [← hgen, ← hEy, ← hgT]; rfl
        rw [h3] at h2
        have h4 := specializes_iff_mem_closure.mp h2
        rw [hyc.closure_eq] at h4
        rw [← hgT]
        exact h4
      have hd : DenseRange π.base := π.denseRange
      have : closure (Set.range π.base) = {y} := by
        rw [show Set.range π.base = {y} from
          Set.eq_singleton_iff_unique_mem.mpr ⟨⟨x, hx⟩, by rintro _ ⟨z, rfl⟩; exact hall z⟩,
          hyc.closure_eq]
      rw [hd.closure_range] at this
      apply hyg
      have hgY : genericPoint Y ∈ (Set.univ : Set Y) := trivial
      rw [this] at hgY
      exact hgY.symm
  have hlt := intersectionNumber_neg_of_isRelativelyAntiAmple g (hqf _)
    hg.isNegativeExtremalContraction.isRelativelyAntiAmple C hCg
  have hA0 : A.intersectionNumber ℂ sX C.ι C.dim_le (hqf A) = 0 := by
    refine intersectionNumber_eq_zero_of_disjoint sX hQ A (hqf A) C fun z hz hzA => ?_
    obtain ⟨E', hE', hzE'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hzA
    have hE's : E' ∈ BX.roundDown.support := by
      refine Finsupp.mem_support_iff.mpr fun h0 => hE' ?_
      change ((BX.roundDown E' : ℤ) : ℚ) = 0
      rw [h0, Int.cast_zero]
    have h1 : π z = y := (hCπ z (specializes_iff_mem_closure.mp hz)).trans hEy
    have h2 := map_eq_of_mem_support π (hAc E' hE's) hzE'
    exact hyS E' hE's (h2.symm.trans h1)
  rw [h.intersectionNumber_eq hQ hYv hπ C hCπ, hA0] at hlt
  simp at hlt

/-- **At a nef endpoint over a curve, a vertical floor is a union of whole fibres.** The lowered
adjoint `K + B - ε⌊B⌋ ≡_Y -ε⌊B⌋` is nef over `Y`, so the effective vertical `⌊B⌋` is anti-nef
over `Y`, hence the pull-back of an effective divisor on `Y`
(`MMP.Fourfold.exists_eq_pullback_of_isVertical_of_isRelativelyNef_neg`), whose support is the
preimage of finitely many points. -/
private theorem exists_floor_eq_preimage_of_isRelativelyNef {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX) {π : X ⟶ Y}
    (hπ : π ≫ sY = sX) (hπp : IsProjectiveMorphism π) (hYp : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hYn : IsNormalVariety ℂ sY) (hY : topologicalKrullDim Y = 1)
    (hO : ∀ U : Y.Opens, IsIso (π.app U)) {A : QDivisor Y} (hAq : A.IsQCartier) {ε : ℚ}
    (hε : 0 < ε ∧ ε < 1) {KX : Divisor X} {BX L : QDivisor X} {c0ne c0vert : Prop}
    (h : ModelInv sX π hAq ε KX BX L c0ne c0vert)
    (hv : QDivisor.IsVertical π (Divisor.toQDivisor BX.roundDown))
    (hnef : IsRelativelyNef ℂ sX π (QDivisor.toRDivisor (Divisor.toQDivisor KX + L))) :
    ∃ F : Set Y, ⋃ E ∈ BX.roundDown.support, (E.support : Set X) = π.base ⁻¹' F := by
  classical
  haveI : IsDominant π := h.dom
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : IsProper sX := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp
    ((MMP.Mori.isProjectiveVariety_iff ℂ sX).mp hX).2).2
  haveI : IsProper π := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hπp).2
  have hYv : MMP.Mori.IsVariety ℂ sY := hYn.1
  haveI : IsIntegral Y := hYv.toIsIntegral
  set A : QDivisor X := Divisor.toQDivisor BX.roundDown with hAdef
  have hA0 : 0 ≤ A := fun E => by
    change (0 : ℚ) ≤ ((BX.roundDown E : ℤ) : ℚ)
    have : (0 : ℚ) ≤ BX E := h.lc.2.1 E
    exact_mod_cast Int.floor_nonneg.mpr this
  have hqf := fun D : QDivisor X => isQCartier_of_isQFactorial sX hQ D
  -- `-A` is nef over `Y`
  have hnef' : (-A).IsRelativelyNef sX π := by
    refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX (hqf _)
      fun C hC => ?_
    have h1 := intersectionNumber_nonneg_of_isRelativelyNef π (hqf _) hnef C hC
    rw [h.intersectionNumber_eq hQ hYv hπ C hC] at h1
    rw [intersectionNumber_congr (k := ℂ) sX C.ι C.dim_le (hqf _) (hqf _)
        (show -A = (-1 : ℚ) • A by rw [neg_one_smul]),
      MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le A (hqf A) (-1) (hqf _)]
    nlinarith [hε.1]
  have hCsm : IsSmoothScheme sY := isSmoothScheme_of_topologicalKrullDim_eq_one hYv hY
  have hcart : ∀ D : Divisor Y, D.IsCartier := isCartier_of_isSmoothScheme hCsm
  have hgen : ∀ (D : Divisor Y) (Z : irreducibleComponents X),
      π (componentGenericPoint X Z) ∉ D.supp := fun D Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' π D Z
  have hfib : ∀ y : Y, _root_.IsPreconnected (π ⁻¹' {y}) := fun y =>
    (π.isConnected_preimage_singleton_of_isIso_app hO y).isPreconnected
  refine ⟨π.base '' ⋃ E ∈ BX.roundDown.support, (E.support : Set X), ?_⟩
  refine Set.Subset.antisymm (fun x hx => ⟨x, hx, rfl⟩) fun x hx => ?_
  obtain ⟨x', hx', hxx'⟩ := hx
  obtain ⟨E, hE, hx'E⟩ := Set.mem_iUnion₂.mp hx'
  have hAE : A E ≠ 0 := by
    change ((BX.roundDown E : ℤ) : ℚ) ≠ 0
    exact_mod_cast Finsupp.mem_support_iff.mp hE
  have hy : π x' = π E.genericPoint := hv E hAE x' hx'E
  -- the image `y` of `E` is a closed point
  have hcl := isClosed_map_genericPoint_of_isVertical π hv hAE
  have hyg : π E.genericPoint ≠ genericPoint Y := fun he =>
    not_isClosed_genericPoint hY (he ▸ hcl)
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (π E.genericPoint)
    (coheight_eq_one_of_ne_genericPoint hY hyg)
  have hP : MMP.Mori.PrimeDivisor.genericPoint P = π E.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hPc : IsClosed ({MMP.Mori.PrimeDivisor.genericPoint P} : Set Y) := by rw [hP]; exact hcl
  set F := Divisor.pullback (f := π) (Finsupp.single P 1 : Divisor Y) (hcart _) (hgen _)
  have hF : Divisor.IsPullback π (Finsupp.single P 1 : Divisor Y) (hgen _) F :=
    Divisor.isPullback_pullback (hcart _) (hgen _)
  obtain ⟨t, -, ht⟩ := exists_coeff_eq_mul_of_isPullback_single sX π hQ hfib P hPc hF A
    hA0 hnef'
  have htpos : t ≠ 0 := by
    intro h0
    apply hAE
    rw [ht E hP.symm, h0, zero_mul]
  have hxF : x ∈ F.supp := mem_supp_of_isPullback_single π P hF (by rw [← hxx', hy, hP])
  obtain ⟨E', hE', hxE'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxF
  have hE'P : π E'.genericPoint = P.genericPoint := by
    by_contra hne
    exact hE' (coeff_eq_zero_of_isPullback_single π P hPc hF E' hne)
  refine Set.mem_iUnion₂.mpr ⟨E', ?_, hxE'⟩
  have hAE' : A E' ≠ 0 := by
    rw [ht E' hE'P]
    exact mul_ne_zero htpos (by exact_mod_cast hE')
  refine Finsupp.mem_support_iff.mpr fun h0 => hAE' ?_
  change ((BX.roundDown E' : ℤ) : ℚ) = 0
  rw [h0, Int.cast_zero]

/-- Along the program, every model has `π_* 𝒪 = 𝒪_Y`: the composite of the steps `S ⟶ X_i` is
proper birational onto the normal `X_i`, so `p_* 𝒪_S = (π_i)_* 𝒪_{X_i}`. -/
private theorem isIso_app_modelMap {S Y : Scheme.{0}} [IsIntegral S] [CompactSpace S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sS : S ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {p : S ⟶ Y} {K : Divisor S}
    {L : QDivisor S} (hp : IsContraction sS sY p) (P : RelativeDltProgram sS sY p K L)
    (hiso : ∀ j : ℕ, (j : ℕ∞) < P.n → IsIso (P.fp j)) :
    ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∀ U : Y.Opens, IsIso ((modelMap p P.πY i).app U)
  | 0, _, U => hp.isIso_app U
  | i + 1, hi, U => by
    have hi' : (i : ℕ∞) < P.n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self i) hi
    have ih := isIso_app_modelMap hp P hiso i hi'.le
    have hstep := P.isElementaryDltStep i hi'
    have hc := hstep.isNegativeRelativeRayContraction.isRelativeContractionOfFace
    haveI := hiso i hi'
    have h1 : IsIso ((P.f i ≫ P.gZ i).app U) := by
      rw [Scheme.Hom.congr_app hc.comp_eq U]
      haveI := ih U
      infer_instance
    rw [Scheme.Hom.comp_app] at h1
    haveI := hc.isIso_app (P.gZ i ⁻¹ᵁ U)
    have hgZ : IsIso ((P.gZ i).app U) :=
      @IsIso.of_isIso_comp_right _ _ _ _ _ ((P.gZ i).app U) ((P.f i).app (P.gZ i ⁻¹ᵁ U))
        inferInstance h1
    have hfp : IsIso ((P.fp i).app (P.gZ i ⁻¹ᵁ U)) := inferInstance
    change IsIso ((P.πY i).app U)
    rw [Scheme.Hom.congr_app hstep.comp_eq.symm U, Scheme.Hom.comp_app]
    simp only [eqToHom_op, eqToHom_map]
    exact IsIso.comp_isIso' (IsIso.comp_isIso' hgZ hfp) inferInstance

/-- **The endpoint of the program.** -/
private theorem endpoint {S Y : Scheme.{0}} [IsIntegral S] [CompactSpace S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y]
    [IsNormal Y]
    {sS : S ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {p : S ⟶ Y} {K : Divisor S}
    {B : QDivisor S} (hp : IsContraction sS sY p) (hYp : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hY : topologicalKrullDim Y ≤ 1) {A : QDivisor Y} (hA : A.IsAmple) (hAq : A.IsQCartier)
    {ε : ℚ} (hε : 0 < ε ∧ ε < 1)
    (P : RelativeDltProgram sS sY p K (B - ε • Divisor.toQDivisor B.roundDown))
    (hP : P.IsProjective) (hn : P.n ≠ ⊤)
    (hend : IsRelativelyNef ℂ (modelStr sS P.sY P.n.toNat) (modelMap p P.πY P.n.toNat)
        (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) +
          divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY P.n.toNat)) ∨ P.hasFinal)
    (h : ModelInv (modelStr sS P.sY P.n.toNat) (modelMap p P.πY P.n.toNat) hAq ε
      (divisorSeq K P.KY P.n.toNat) (iterTransform P.φ B P.n.toNat)
      (divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY P.n.toNat)
      (B.roundDown ≠ 0) (QDivisor.IsVertical p (Divisor.toQDivisor B.roundDown)))
    (hO : ∀ U : Y.Opens, IsIso ((modelMap p P.πY P.n.toNat).app U)) :
    ((¬ QDivisor.IsVertical p (Divisor.toQDivisor B.roundDown) ∨
        (topologicalKrullDim Y = 0 ∧ B.roundDown ≠ 0)) → P.hasFinal) ∧
    (topologicalKrullDim Y = 1 → QDivisor.IsVertical p (Divisor.toQDivisor B.roundDown) →
      ¬ P.hasFinal ∧ ∃ F : Set Y,
        ⋃ E ∈ (iterTransform P.φ B P.n.toNat).roundDown.support, (E.support : Set _) =
          (modelMap p P.πY P.n.toNat).base ⁻¹' F) := by
  classical
  have hnn : ((P.n.toNat : ℕ) : ℕ∞) ≤ P.n := by rw [ENat.coe_toNat hn]
  have hm := P.isRelativeDltModel _ hnn
  have hXp := hP.2 _ hnn
  refine ⟨fun hcase => ?_, fun hY1 hv => ?_⟩
  · by_contra hnf
    have hnef := hend.resolve_right hnf
    refine not_isRelativelyNef_of_not_isVertical hXp hm.isQFactorial hm.comp_eq
      hm.isProjectiveMorphism hYp hY hAq hε h ?_ hnef
    rcases hcase with hc | ⟨h0, hc⟩
    · exact Or.inl (h.horiz hc)
    · exact Or.inr ⟨h0, h.ne hc⟩
  · have hvX := h.vert hv
    have hnf : ¬ P.hasFinal := fun hf => by
      obtain ⟨-, hg, hdim⟩ := P.final_spec hf
      exact false_of_isNegativeRelativeRayContraction_of_isVertical hXp hm.isQFactorial
        hm.comp_eq hm.isProjectiveMorphism hYp hY1 hAq hε h hvX hg hdim
    refine ⟨hnf, ?_⟩
    have hnef := hend.resolve_right hnf
    exact exists_floor_eq_preimage_of_isRelativelyNef hXp hm.isQFactorial hm.comp_eq
      hm.isProjectiveMorphism hYp hp.isNormalVariety_target hY1
      hO hAq hε h hvX hnef

private theorem solution
    {S Y : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sS : S ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hdim : topologicalKrullDim S = 2)
    (hQ : IsQFactorial sS) {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2) {B : QDivisor S}
    (hB : MMP.Intersection.IsDltPair sS B)
    {p : S ⟶ Y} (hp : IsContraction sS sY p) (hYp : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hY : topologicalKrullDim Y ≤ 1) {A : QDivisor Y} (hA : A.IsAmple)
    (hDA : ∃ (hAq : A.IsQCartier)
      (hη : ∀ Z : irreducibleComponents S, p (componentGenericPoint S Z) ∉ A.supp),
      (Divisor.toQDivisor K + B).QLinearlyEquivalent (A.pullback hAq hη))
    (ε : ℚ) (hε : 0 < ε ∧ ε < 1) :
    ∃ (P : RelativeDltProgram sS sY p K (B - ε • Divisor.toQDivisor B.roundDown))
      (BU : ∀ i, QDivisor (P.Y i)),
      P.n ≠ ⊤ ∧ P.IsProjective ∧ P.IsMaximal ∧
      (∀ i : ℕ, (i : ℕ∞) < P.n →
        BU i = MMP.Mori.RationalMap.transformDivisor (P.φ i) (divisorSeq B BU i)) ∧
      (∀ i : ℕ, (i : ℕ∞) ≤ P.n →
        divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY i =
            divisorSeq B BU i - ε • Divisor.toQDivisor (divisorSeq B BU i).roundDown ∧
          MMP.Fourfold.IsKltPair (modelStr sS P.sY i)
            (divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY i) ∧
          MMP.Intersection.IsLogCanonicalPair (modelStr sS P.sY i) (divisorSeq B BU i)) ∧
      (∀ i : ℕ, (i : ℕ∞) < P.n →
        IsBirationalMorphism (P.f i) ∧
          (∃ E : MMP.Mori.PrimeDivisor (modelSeq S P.Y i),
            (MMP.Mori.exceptionalSet (P.f i) : Set (modelSeq S P.Y i)) = E.support) ∧
          IsIso (P.fp i) ∧
          ∃ q : modelSeq S P.Y i ⟶ P.Y i, q ≫ P.fp i = P.f i ∧
            (∃ (hqY : IsNormalVariety ℂ (q ≫ P.sY i)) (hq : IsBirationalMorphism q),
              MMP.Mori.IsCrepantBoundary (P.sY i) 2 (P.KY i) (BU i) q hqY hq
                (divisorSeq B BU i)) ∧
            ∀ (T T' : Scheme.{0}) (ι : T ⟶ modelSeq S P.Y i) (ι' : T' ⟶ P.Y i)
              [IsClosedImmersion ι] [IsReduced T] [IsClosedImmersion ι'] [IsReduced T'],
              Set.range ι.base =
                  ⋃ E ∈ (divisorSeq B BU i).roundDown.support, (E.support : Set _) →
              Set.range ι'.base = ⋃ E ∈ (BU i).roundDown.support, (E.support : Set _) →
              (∃ h : T ⟶ T', h ≫ ι' = ι ≫ q) ∧
              ∀ h : T ⟶ T', h ≫ ι' = ι ≫ q →
                (∀ U : T'.Opens, IsIso (h.app U)) ∧ ∀ t : T', _root_.IsConnected (h.base ⁻¹' {t})) ∧
      ((¬ QDivisor.IsVertical p (Divisor.toQDivisor B.roundDown) ∨
          (topologicalKrullDim Y = 0 ∧ B.roundDown ≠ 0)) → P.hasFinal) ∧
      (topologicalKrullDim Y = 1 → QDivisor.IsVertical p (Divisor.toQDivisor B.roundDown) →
        ¬ P.hasFinal ∧ ∃ F : Set Y,
          ⋃ E ∈ (divisorSeq B BU P.n.toNat).roundDown.support, (E.support : Set _) =
            (modelMap p P.πY P.n.toNat).base ⁻¹' F) := by
  classical
  haveI : IsIntegral Y := hYp.1.toIsIntegral
  obtain ⟨hAq, hη, hDAeq⟩ := hDA
  have hL := isDltPair_sub_smul_roundDown hQ hB hε.1 hε.2.le
  obtain ⟨-, hP3⟩ := projectiveLowerLogMMP_three
  obtain ⟨-, -, P, hproj, hn, hend⟩ := hP3 S Y sS sY p K _ hS hYp hp.comp_eq
    (by rw [hdim]; exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3)) hQ ⟨2, hK⟩ hL
  set BU : ∀ i, QDivisor (P.Y i) := fun i => iterTransform P.φ B (i + 1) with hBU
  have hseq : ∀ i, divisorSeq B BU i = iterTransform P.φ B i := divisorSeq_iterTransform P.φ B
  -- the invariant along the program
  have hinv : ∀ i : ℕ, (i : ℕ∞) ≤ P.n →
      ModelInv (modelStr sS P.sY i) (modelMap p P.πY i) hAq ε (divisorSeq K P.KY i)
        (iterTransform P.φ B i) (divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY i)
        (B.roundDown ≠ 0) (QDivisor.IsVertical p (Divisor.toQDivisor B.roundDown)) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact
        { lowered := rfl
          lc := hB.1
          dim := hdim
          adj := ⟨hη, hDAeq⟩
          ne := id
          dom := ⟨hp.surjective.denseRange⟩
          vert := id
          horiz := id }
    | succ i ih =>
      intro hi
      have hi' : (i : ℕ∞) < P.n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self i) hi
      exact (step hAq hε P hproj i hi' (ih hi'.le)).2
  refine ⟨P, BU, hn, hproj, ?_, fun i _ => ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rcases hend with h | h
    · exact Or.inr (Or.inl ⟨hn, h⟩)
    · exact Or.inr (Or.inr h)
  · rw [hseq]; rfl
  · have h := hinv i hi
    rw [hseq]
    exact ⟨h.lowered, isKltPair_of_modelInv hε h (P.isRelativeDltModel i hi).isDltPair, h.lc⟩
  · rw [hseq]
    exact (step hAq hε P hproj i hi (hinv i hi.le)).1
  · have hnn : ((P.n.toNat : ℕ) : ℕ∞) ≤ P.n := by
      rw [ENat.coe_toNat hn]
    rw [hseq]
    refine endpoint hp hYp hY hA hAq hε P hproj hn hend (hinv _ hnn)
      (isIso_app_modelMap hp P (fun j hj => (step hAq hε P hproj j hj (hinv j hj.le)).1.2.2.1)
        _ hnn)

end Proof_lem_mmp_surface_semiample_floor_lowering_program

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **A central-crepant floor-lowering surface program.** Let `(S, B)` be a `ℚ`-factorial
projective dlt complex surface, `C = ⌊B⌋`, and let `p : S ⟶ Y` be a contraction onto a normal
projective variety with `dim Y ≤ 1` such that `K_S + B ∼_ℚ p^*A` for an ample `ℚ`-divisor `A`
on `Y`. For every rational `0 < ε < 1` there is a projective relative dlt program `P` over `Y`
for `(S, B - εC)` with finitely many steps, maximal, together with the birational transforms
`B_i` of `B`, such that
* each model has lowered boundary `B_i - ε⌊B_i⌋`, which is klt, and `(S_i, B_i)` is lc;
* each step is a divisorial contraction `q_i : S_i ⟶ S_{i+1}` (`q_i ≫ f_i⁺ = f_i`), crepant
  (`MMP.Mori.IsCrepantBoundary`) for `K + B_i`, and a morphism `h` of the reduced floors over
  `q_i` exists, and it satisfies `𝒪 = h_* 𝒪` and has connected fibres;
* if `C` is not vertical over `Y`, or `Y` is a point and `C ≠ 0`, the program ends with a Mori
  fibre contraction over `Y`;
* if `Y` is a curve and `C` is vertical, the endpoint is nef over `Y` and its floor is the
  preimage of a set of points of `Y`. -/
@[mmp "lem_mmp_surface_semiample_floor_lowering_program"]
public theorem IsContraction.exists_relativeDltProgram_sub_smul_roundDown
    {S Y : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sS : S ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hdim : topologicalKrullDim S = 2)
    (hQ : IsQFactorial sS) {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2) {B : QDivisor S}
    (hB : MMP.Intersection.IsDltPair sS B)
    {p : S ⟶ Y} (hp : IsContraction sS sY p) (hYp : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hY : topologicalKrullDim Y ≤ 1) {A : QDivisor Y} (hA : A.IsAmple)
    (hDA : ∃ (hAq : A.IsQCartier)
      (hη : ∀ Z : irreducibleComponents S, p (componentGenericPoint S Z) ∉ A.supp),
      (Divisor.toQDivisor K + B).QLinearlyEquivalent (A.pullback hAq hη))
    (ε : ℚ) (hε : 0 < ε ∧ ε < 1) :
    ∃ (P : RelativeDltProgram sS sY p K (B - ε • Divisor.toQDivisor B.roundDown))
      (BU : ∀ i, QDivisor (P.Y i)),
      P.n ≠ ⊤ ∧ P.IsProjective ∧ P.IsMaximal ∧
      (∀ i : ℕ, (i : ℕ∞) < P.n →
        BU i = MMP.Mori.RationalMap.transformDivisor (P.φ i) (divisorSeq B BU i)) ∧
      (∀ i : ℕ, (i : ℕ∞) ≤ P.n →
        divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY i =
            divisorSeq B BU i - ε • Divisor.toQDivisor (divisorSeq B BU i).roundDown ∧
          MMP.Fourfold.IsKltPair (modelStr sS P.sY i)
            (divisorSeq (B - ε • Divisor.toQDivisor B.roundDown) P.BY i) ∧
          MMP.Intersection.IsLogCanonicalPair (modelStr sS P.sY i) (divisorSeq B BU i)) ∧
      (∀ i : ℕ, (i : ℕ∞) < P.n →
        IsBirationalMorphism (P.f i) ∧
          (∃ E : MMP.Mori.PrimeDivisor (modelSeq S P.Y i),
            (MMP.Mori.exceptionalSet (P.f i) : Set (modelSeq S P.Y i)) = E.support) ∧
          IsIso (P.fp i) ∧
          ∃ q : modelSeq S P.Y i ⟶ P.Y i, q ≫ P.fp i = P.f i ∧
            (∃ (hqY : IsNormalVariety ℂ (q ≫ P.sY i)) (hq : IsBirationalMorphism q),
              MMP.Mori.IsCrepantBoundary (P.sY i) 2 (P.KY i) (BU i) q hqY hq
                (divisorSeq B BU i)) ∧
            ∀ (T T' : Scheme.{0}) (ι : T ⟶ modelSeq S P.Y i) (ι' : T' ⟶ P.Y i)
              [IsClosedImmersion ι] [IsReduced T] [IsClosedImmersion ι'] [IsReduced T'],
              Set.range ι.base =
                  ⋃ E ∈ (divisorSeq B BU i).roundDown.support, (E.support : Set _) →
              Set.range ι'.base = ⋃ E ∈ (BU i).roundDown.support, (E.support : Set _) →
              (∃ h : T ⟶ T', h ≫ ι' = ι ≫ q) ∧
              ∀ h : T ⟶ T', h ≫ ι' = ι ≫ q →
                (∀ U : T'.Opens, IsIso (h.app U)) ∧ ∀ t : T', _root_.IsConnected (h.base ⁻¹' {t})) ∧
      ((¬ QDivisor.IsVertical p (Divisor.toQDivisor B.roundDown) ∨
          (topologicalKrullDim Y = 0 ∧ B.roundDown ≠ 0)) → P.hasFinal) ∧
      (topologicalKrullDim Y = 1 → QDivisor.IsVertical p (Divisor.toQDivisor B.roundDown) →
        ¬ P.hasFinal ∧ ∃ F : Set Y,
          ⋃ E ∈ (divisorSeq B BU P.n.toNat).roundDown.support, (E.support : Set _) =
            (modelMap p P.πY P.n.toNat).base ⁻¹' F) :=
              by revert S Y sS sY hS hdim hQ K hK B hB p hp hYp hY A hA hDA ε hε; first | exact Proof_lem_mmp_surface_semiample_floor_lowering_program.solution | exact Proof_lem_mmp_surface_semiample_floor_lowering_program.solution _ | exact Proof_lem_mmp_surface_semiample_floor_lowering_program.solution _ _ | exact Proof_lem_mmp_surface_semiample_floor_lowering_program.solution _ _ _ | exact Proof_lem_mmp_surface_semiample_floor_lowering_program.solution _ _ _ _

end MMP.Fourfold
