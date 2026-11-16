module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksBundleCharts
public import Mathlib.Topology.VectorBundle.Basic
/-!
# A Stacks vector bundle as a complex topological vector bundle

Let `X` be a scheme over `ℂ` and `ℰ` a quasi-coherent `𝒪_X`-module, finite locally free of rank
`r`, with vector bundle `π : 𝐕(ℰ) ⟶ X` (`MMP.Modules.totalSpace`, `MMP.Modules.proj`). On
`ℂ`-points with the classical topology, `π : 𝐕(ℰ)(ℂ) → X(ℂ)` is a complex topological vector
bundle with fibre `ℂʳ`:

* a chart `c = (V, b)` (`MMP.Modules.Chart`) gives a homeomorphism `π⁻¹V(ℂ) ≅ V(ℂ) × ℂʳ`
  (`MMP.Modules.chartHomeomorph`);
* on `π⁻¹(V ∩ V')(ℂ)` the coordinates of two charts are related by the transition matrix at the
  base point (`MMP.Modules.coord_eq_transition_mulVec`), so the fibre over `x` is a complex vector
  space through any chart, and the coordinate changes are continuous
  (`MMP.Modules.continuousOn_transition`).

This file makes `𝐕(ℰ)(ℂ) → X(ℂ)` a Mathlib vector bundle
`Bundle.VectorBundle ℂ (Fin r → ℂ) (MMP.Modules.Fibre E r)`, with total space homeomorphic to
`𝐕(ℰ)(ℂ)`.

## Main definitions

* `MMP.Modules.chartBase c`: the open set `V(ℂ) ⊆ X(ℂ)` of a chart `c = (V, b)`.
* `MMP.Modules.chartAt E r x`: a chart around `x ∈ X(ℂ)`.
* `MMP.Modules.Fibre E r x`: the fibre `π⁻¹(x)`, a complex vector space.
* `MMP.Modules.fibreCoord c x`: the coordinates of a chart, as a linear map on the fibre.
* `MMP.Modules.totalSpaceHomeomorph E r`: the total space of the topological bundle is
  `𝐕(ℰ)(ℂ)`.
* `MMP.Modules.chartTrivialization c`: the trivialization over `V(ℂ)` given by the chart `c`.

## Main results

* the instances `FiberBundle (Fin r → ℂ) (Fibre E r)` and
  `VectorBundle ℂ (Fin r → ℂ) (Fibre E r)`.

## Implementation notes

The rank `r` is an explicit argument of `Fibre`: the linear structure on a fibre is read off a
chart of rank `r`, and `r` is not determined by `E` when `X` is empty.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology Bundle
open scoped Matrix

namespace MMP.Modules

open UnderlyingSpace

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] {E : X.Modules} [E.IsQuasicoherent] {r : ℕ}

/-- The open set `V(ℂ) ⊆ X(ℂ)` of the points lying in the domain `V` of a chart `c = (V, b)`. -/
def chartBase (c : Chart E r) : Set (UnderlyingSpace ℂ X) :=
  {x | ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1}

omit [E.IsQuasicoherent] in
/-- The set `V(ℂ)` of a chart `c = (V, b)` is open in `X(ℂ)`. -/
lemma isOpen_chartBase (c : Chart E r) : IsOpen (chartBase c) :=
  isOpen_setOf_le_preimage _

omit [E.IsQuasicoherent] in
/-- A point lies in `V(ℂ) ∩ V'(ℂ)` if and only if it lies in `(V ∩ V')(ℂ)`. -/
lemma mem_chartBase_inter_iff (c c' : Chart E r) (x : UnderlyingSpace ℂ X) :
    x ∈ chartBase c ∩ chartBase c' ↔ ⊤ ≤ x.toHom ⁻¹ᵁ (c.1.1 ⊓ c'.1.1) :=
  ⟨fun h _ hz ↦ ⟨h.1 hz, h.2 hz⟩, fun h ↦ ⟨fun _ hz ↦ (h hz).1, fun _ hz ↦ (h hz).2⟩⟩

/-- A point of `𝐕(ℰ)(ℂ)` over `(V ∩ V')(ℂ)` lies in `π⁻¹(V ∩ V')(ℂ)`. -/
lemma top_le_preimage_proj_inf {c c' : Chart E r} {p : UnderlyingSpace ℂ (totalSpace E)}
    (h : mapFun (proj E) p ∈ chartBase c ∩ chartBase c') :
    ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ (c.1.1 ⊓ c'.1.1)) :=
  (mem_chartBase_inter_iff c c' (mapFun (proj E) p)).1 h

variable (E) in
/-- The fibre `π⁻¹(x)` of `𝐕(ℰ)(ℂ) → X(ℂ)` over a point `x ∈ X(ℂ)`. Its linear structure comes
from the charts of rank `r`, which is why `r` is an argument. -/
@[nolint unusedArguments]
def Fibre (_r : ℕ) (x : UnderlyingSpace ℂ X) : Type :=
  {p : UnderlyingSpace ℂ (totalSpace E) // mapFun (proj E) p = x}

/-- The fibre carries the subspace topology of `𝐕(ℰ)(ℂ)`. -/
instance (x : UnderlyingSpace ℂ X) : TopologicalSpace (Fibre E r x) :=
  inferInstanceAs (TopologicalSpace {p : UnderlyingSpace ℂ (totalSpace E) // mapFun (proj E) p = x})

variable (E r) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

/-- Every point of `X(ℂ)` lies in `V(ℂ)` for some chart `c = (V, b)` of rank `r`. -/
lemma exists_mem_chartBase (x : UnderlyingSpace ℂ X) : ∃ c : Chart E r, x ∈ chartBase c := by
  obtain ⟨c, hc⟩ := exists_chart_mem (E := E) r (x.toHom (IsLocalRing.closedPoint ℂ))
  exact ⟨c, (top_le_preimage_iff x _).2 hc⟩

/-- A chart around a point of `X(ℂ)`. -/
def chartAt (x : UnderlyingSpace ℂ X) : Chart E r :=
  (exists_mem_chartBase E r x).choose

/-- A point `x ∈ X(ℂ)` lies in the domain of the chart `chartAt E r x`. -/
lemma mem_chartBase_chartAt (x : UnderlyingSpace ℂ X) : x ∈ chartBase (chartAt E r x) :=
  (exists_mem_chartBase E r x).choose_spec

/-! ### The fibres -/

variable {E r}

/-- The point of the fibre over `x ∈ V(ℂ)` with coordinates `w` in the chart `c`. -/
def fibreChartInv (c : Chart E r) (x : UnderlyingSpace ℂ X) (hx : x ∈ chartBase c)
    (w : Fin r → ℂ) : Fibre E r x :=
  ⟨chartInv c x hx w, mapFun_proj_chartInv c x hx w⟩

/-- For `x ∈ V(ℂ)`, the coordinates of a chart `c` identify the fibre over `x` with `ℂʳ`. -/
def fibreEquiv (c : Chart E r) (x : UnderlyingSpace ℂ X) (hx : x ∈ chartBase c) :
    Fibre E r x ≃ (Fin r → ℂ) where
  toFun p := coord c p.1
  invFun w := fibreChartInv c x hx w
  left_inv p := Subtype.ext (by
    obtain ⟨p, rfl⟩ := p
    exact chartInv_mapFun_proj_coord c p hx)
  right_inv w := coord_chartInv c x hx w

variable (E r) in
/-- The fibres are additive groups, through the coordinates of the chart `chartAt E r x`; the
structure does not depend on the chart, as the transitions are linear (`fibreCoord`). -/
instance (x : UnderlyingSpace ℂ X) : AddCommGroup (Fibre E r x) :=
  (fibreEquiv (chartAt E r x) x (mem_chartBase_chartAt E r x)).addCommGroup

variable (E r) in
/-- The coordinates of the chart `chartAt E r x`, as an additive isomorphism with `ℂʳ`. -/
def fibreAddEquiv (x : UnderlyingSpace ℂ X) : Fibre E r x ≃+ (Fin r → ℂ) :=
  (fibreEquiv (chartAt E r x) x (mem_chartBase_chartAt E r x)).addEquiv

variable (E r) in
/-- The fibres are complex vector spaces, through the coordinates of a chart. -/
instance (x : UnderlyingSpace ℂ X) : Module ℂ (Fibre E r x) :=
  AddEquiv.module ℂ (fibreAddEquiv E r x)

variable (E r) in
/-- The coordinates of the chart `chartAt E r x`, as a linear isomorphism with `ℂʳ`. -/
def fibreLinearEquiv (x : UnderlyingSpace ℂ X) : Fibre E r x ≃ₗ[ℂ] (Fin r → ℂ) :=
  AddEquiv.linearEquiv ℂ (fibreAddEquiv E r x)

/-- The coordinates of any chart `c` on the fibre over `x`, as a linear map: they are the
transition matrix from `chartAt E r x` to `c` at `x` times the coordinates of `chartAt E r x`. For
`x ∈ V(ℂ)` they are the coordinates of `c` (`fibreCoord_apply`). -/
def fibreCoord (c : Chart E r) (x : UnderlyingSpace ℂ X) : Fibre E r x →ₗ[ℂ] (Fin r → ℂ) :=
  (transition (chartAt E r x) c x).mulVecLin ∘ₗ (fibreLinearEquiv E r x).toLinearMap

/-- For `x ∈ V(ℂ)`, `fibreCoord c x` is given by the coordinates of the chart `c`. -/
lemma fibreCoord_apply (c : Chart E r) (x : UnderlyingSpace ℂ X) (hx : x ∈ chartBase c)
    (y : Fibre E r x) : fibreCoord c x y = coord c y.1 := by
  obtain ⟨p, rfl⟩ := y
  change transition (chartAt E r _) c _ *ᵥ coord (chartAt E r _) p = coord c p
  exact (coord_eq_transition_mulVec (chartAt E r _) c p
    (top_le_preimage_proj_inf ⟨mem_chartBase_chartAt E r _, hx⟩)).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] in
/-- Two points of a fibre over `V(ℂ)` with the same coordinates in the chart `c` are equal. -/
lemma fibre_ext (c : Chart E r) {x : UnderlyingSpace ℂ X} (hx : x ∈ chartBase c)
    {y y' : Fibre E r x} (h : coord c y.1 = coord c y'.1) : y = y' :=
  (fibreEquiv c x hx).injective h

/-! ### The total space -/

variable (E r) in
/-- The total space `Σ x, π⁻¹(x)` is `𝐕(ℰ)(ℂ)`. -/
def totalSpaceEquiv : TotalSpace (Fin r → ℂ) (Fibre E r) ≃ UnderlyingSpace ℂ (totalSpace E) where
  toFun p := p.2.1
  invFun q := ⟨mapFun (proj E) q, ⟨q, rfl⟩⟩
  left_inv := by
    rintro ⟨x, p, rfl⟩
    rfl
  right_inv _ := rfl

/-- The topology of the total space is that of `𝐕(ℰ)(ℂ)`. -/
instance : TopologicalSpace (TotalSpace (Fin r → ℂ) (Fibre E r)) :=
  .induced (totalSpaceEquiv E r) inferInstance

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] in
variable (E r) in
/-- The identification `totalSpaceEquiv E r` of the total space with `𝐕(ℰ)(ℂ)` is inducing. -/
lemma isInducing_totalSpaceEquiv : IsInducing (totalSpaceEquiv E r) :=
  ⟨rfl⟩

variable (E r) in
/-- The total space of the topological bundle is homeomorphic to `𝐕(ℰ)(ℂ)`. -/
def totalSpaceHomeomorph :
    TotalSpace (Fin r → ℂ) (Fibre E r) ≃ₜ UnderlyingSpace ℂ (totalSpace E) :=
  (totalSpaceEquiv E r).toHomeomorphOfIsInducing (isInducing_totalSpaceEquiv E r)

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] in
/-- `totalSpaceHomeomorph E r` sends a point of a fibre to the underlying point of `𝐕(ℰ)(ℂ)`. -/
lemma totalSpaceHomeomorph_apply (p : TotalSpace (Fin r → ℂ) (Fibre E r)) :
    totalSpaceHomeomorph E r p = p.2.1 :=
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] in
/-- The bundle projection of a point of the total space is `π` of the corresponding point of
`𝐕(ℰ)(ℂ)`. -/
lemma proj_eq (p : TotalSpace (Fin r → ℂ) (Fibre E r)) :
    p.proj = mapFun (proj E) (totalSpaceEquiv E r p) :=
  p.2.2.symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] in
variable (E r) in
/-- The identification `totalSpaceEquiv E r` of the total space with `𝐕(ℰ)(ℂ)` is continuous. -/
lemma continuous_totalSpaceEquiv : Continuous (totalSpaceEquiv E r) :=
  (isInducing_totalSpaceEquiv E r).continuous

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] in
variable (E r) in
/-- The bundle projection `TotalSpace (Fin r → ℂ) (Fibre E r) → X(ℂ)` is continuous. -/
lemma continuous_totalSpace_proj :
    Continuous (TotalSpace.proj : TotalSpace (Fin r → ℂ) (Fibre E r) → _) :=
  ((continuous_mapFun _).comp (continuous_totalSpaceEquiv E r)).congr fun p ↦ (proj_eq p).symm

/-! ### The trivializations -/

open Classical in
/-- The point over `x` with coordinates `w` in the chart `c` (`0` when `x ∉ V(ℂ)`). -/
def chartFibrePoint (c : Chart E r) (x : UnderlyingSpace ℂ X) (w : Fin r → ℂ) : Fibre E r x :=
  if hx : x ∈ chartBase c then fibreChartInv c x hx w else 0

/-- For `x ∈ V(ℂ)`, `chartFibrePoint c x w` is the point with coordinates `w` in the chart `c`. -/
lemma chartFibrePoint_of_mem (c : Chart E r) {x : UnderlyingSpace ℂ X} (hx : x ∈ chartBase c)
    (w : Fin r → ℂ) : chartFibrePoint c x w = fibreChartInv c x hx w :=
  dite_eq_left hx

/-- The local trivialization of `𝐕(ℰ)(ℂ) → X(ℂ)` over `V(ℂ)` given by the chart `c = (V, b)`:
`p ↦ (π p, coord c p)`, with inverse `(x, w) ↦ chartInv c x _ w` (the chart homeomorphism
`chartHomeomorph c`). -/
def chartTrivialization (c : Chart E r) :
    Trivialization (Fin r → ℂ) (TotalSpace.proj : TotalSpace (Fin r → ℂ) (Fibre E r) → _) where
  toFun p := (p.proj, coord c p.2.1)
  invFun z := ⟨z.1, chartFibrePoint c z.1 z.2⟩
  source := TotalSpace.proj ⁻¹' chartBase c
  target := chartBase c ×ˢ univ
  map_source' p hp := ⟨hp, mem_univ _⟩
  map_target' z hz := hz.1
  left_inv' p hp := by
    obtain ⟨x, q, rfl⟩ := p
    apply (totalSpaceEquiv E r).injective
    change (chartFibrePoint c (mapFun (proj E) q) (coord c q)).1 = q
    rw [chartFibrePoint_of_mem c hp]
    exact chartInv_mapFun_proj_coord c q hp
  right_inv' z hz := by
    obtain ⟨x, w⟩ := z
    change (x, coord c (chartFibrePoint c x w).1) = (x, w)
    rw [chartFibrePoint_of_mem c hz.1]
    exact Prod.ext rfl (coord_chartInv c x hz.1 w)
  open_source := (isOpen_chartBase c).preimage (continuous_totalSpace_proj E r)
  open_target := (isOpen_chartBase c).prod isOpen_univ
  continuousOn_toFun := by
    refine (continuous_totalSpace_proj E r).continuousOn.prodMk ?_
    refine (continuousOn_coord c).comp (continuous_totalSpaceEquiv E r).continuousOn ?_
    intro p hp
    change mapFun (proj E) (totalSpaceEquiv E r p) ∈ chartBase c
    rwa [← proj_eq]
  continuousOn_invFun := by
    refine (isInducing_totalSpaceEquiv E r).continuousOn_iff.2 ?_
    rw [continuousOn_iff_continuous_domRestrict]
    refine ((continuous_chartInv c).comp
      (((continuous_fst.comp continuous_subtype_val).subtype_mk fun z ↦ z.2.1).prodMk
        (continuous_snd.comp continuous_subtype_val))).congr fun z ↦ ?_
    change chartInv c z.1.1 z.2.1 z.1.2 = (chartFibrePoint c z.1.1 z.1.2).1
    rw [chartFibrePoint_of_mem c z.2.1]
    rfl
  baseSet := chartBase c
  open_baseSet := isOpen_chartBase c
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The trivialization of a chart `c` sends `p` to `(π p, coord c p)`. -/
lemma chartTrivialization_apply (c : Chart E r) (p : TotalSpace (Fin r → ℂ) (Fibre E r)) :
    chartTrivialization c p = (p.proj, coord c p.2.1) :=
  rfl

/-- The base set of the trivialization of a chart `c = (V, b)` is `V(ℂ)`. -/
lemma chartTrivialization_baseSet (c : Chart E r) :
    (chartTrivialization c).baseSet = chartBase c :=
  rfl

/-- `𝐕(ℰ)(ℂ) → X(ℂ)` is a fibre bundle with fibre `ℂʳ`, trivialized by the charts. -/
instance instFiberBundleFibre : FiberBundle (Fin r → ℂ) (Fibre E r) where
  totalSpaceMk_isInducing' _ :=
    ((isInducing_totalSpaceEquiv E r).of_comp_iff).1 IsInducing.subtypeVal
  trivializationAtlas' := range chartTrivialization
  trivializationAt' x := chartTrivialization (chartAt E r x)
  mem_baseSet_trivializationAt' x := mem_chartBase_chartAt E r x
  trivialization_mem_atlas' _ := ⟨_, rfl⟩

/-- The trivialization of a chart is linear on each fibre. -/
instance isLinear_chartTrivialization (c : Chart E r) : (chartTrivialization c).IsLinear ℂ where
  linear x hx := by
    convert (fibreCoord c x).isLinear using 1
    exact funext fun y ↦ (fibreCoord_apply c x hx y).symm

/-- The coordinate change between the trivializations of two charts `c`, `c'` is the transition
matrix: `coord c' = transition c c' x *ᵥ coord c`. -/
lemma coordChangeL_chartTrivialization_apply (c c' : Chart E r) {x : UnderlyingSpace ℂ X}
    (hx : x ∈ chartBase c ∩ chartBase c') (w : Fin r → ℂ) :
    Trivialization.coordChangeL ℂ (chartTrivialization c) (chartTrivialization c') x w =
      transition c c' x *ᵥ w := by
  rw [Trivialization.coordChangeL_apply _ _ hx]
  have h1 : coord c ((chartTrivialization c).symm x w).1 = w :=
    congrArg Prod.snd ((chartTrivialization c).apply_mk_symm hx.1 w)
  have hy : mapFun (proj E) ((chartTrivialization c).symm x w).1 = x :=
    ((chartTrivialization c).symm x w).2
  change coord c' ((chartTrivialization c).symm x w).1 = _
  rw [coord_eq_transition_mulVec c c' _ (top_le_preimage_proj_inf (c := c) (c' := c')
    (p := ((chartTrivialization c).symm x w).1) (by rwa [hy])), hy, h1]

/-- `𝐕(ℰ)(ℂ) → X(ℂ)` is a complex topological vector bundle of rank `r`. -/
instance instVectorBundleFibre : _root_.VectorBundle ℂ (Fin r → ℂ) (Fibre E r) where
  trivialization_linear' e he := by
    obtain ⟨c, rfl⟩ := he.out
    infer_instance
  continuousOn_coordChange' e e' he he' := by
    obtain ⟨c, rfl⟩ := he.out
    obtain ⟨c', rfl⟩ := he'.out
    refine continuousOn_clm_apply.2 fun w ↦ ?_
    refine ContinuousOn.congr ?_ fun x hx ↦ coordChangeL_chartTrivialization_apply c c' hx w
    have hT : ContinuousOn (transition c c') (chartBase c ∩ chartBase c') :=
      (continuousOn_transition c c').mono fun x hx ↦ (mem_chartBase_inter_iff c c' x).1 hx
    refine continuousOn_pi.2 fun a ↦ ?_
    simp only [Matrix.mulVec, dotProduct]
    refine continuousOn_finsetSum _ fun b _ ↦ ?_
    exact (((continuous_apply b).comp (continuous_apply a)).comp_continuousOn hT).mul
      continuousOn_const

end MMP.Modules
