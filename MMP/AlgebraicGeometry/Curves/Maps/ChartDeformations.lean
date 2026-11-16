module

public import MMP.AlgebraicGeometry.Curves.Maps.Deformations

/-!
# Čech deformation theory of marked curve maps over Artinian bases

Let `f : C → U` be a map from a proper curve over a field `k` to a smooth variety, with marked
points `B ⊆ C`, and let `R` be the local ring at `[f]` of a space of maps. Cover `C` by finitely
many affine charts `Spec O_i` mapping into smooth affine charts `Spec S_i` of the target, with
formally étale restrictions on the intersections. For an `A`-point of `R` (`A` a local Artinian
`k`-algebra with residue field `k`) and a small extension `B → A` with kernel `J`, the lifting
problem splits into two stages.

* First stage: on each intersection the lifts `S_s → O_s ⊗ B` of the given map that are fixed
  on the marked points form a torsor under the derivations `S_s → J ⊗ 𝔟_s`; these torsors glue to
  a Čech torsor whose presheaf of derivations has `Ȟ¹ ≅ Ȟ¹(Der(S_·, 𝔟_·)) ⊗ J`. With
  `Ȟ¹(Der(S_·, 𝔟_·)) ≅ H¹(C, f^* T_U(-B))` the first obstruction lies in `H¹(C, f^* T_U(-B)) ⊗ J`.
* Second stage: given a compatible family of local lifts, the transition functions of the fixed
  line bundle and of the pulled-back one agree modulo `J`; their ratio is a Čech cocycle of
  `J ⊗ O_·`, with class in `Ȟ¹(O_·) ⊗ J ≅ H¹(C, 𝒪_C) ⊗ J`. When it vanishes, the local lifts
  and the frames glue to a tuple of sections over `B`, and the universal property of `R` gives
  a lift of the point.

Both obstructions are natural in the quotients of `J`. Packaged as a `ChartSystem`, these data
give a two-stage obstruction theory at `[f]`, which bounds the local dimension of the space of
maps from below by `h⁰ - h¹(f^* T_U(-B)) - h¹(𝒪_C)`.

## Main definitions

* `MMP.Fourfold.CurveChartDeformations.CurveCharts`: the charts of the curve map.
* `MMP.Fourfold.CurveChartDeformations.CurvePoint`: an `A`-point of the curve map on the charts.
* `MMP.Fourfold.CurveChartDeformations.stageOne`,
  `MMP.Fourfold.CurveChartDeformations.stageTwo`: the two lifting problems along a small
  extension.
* `MMP.Fourfold.CurveChartDeformations.thetaOne`,
  `MMP.Fourfold.CurveChartDeformations.thetaTwo`: the identifications of their `Ȟ¹` with
  `V₁ ⊗ J` and `V₂ ⊗ J`.
* `MMP.Fourfold.CurveChartDeformations.Cech.tensorH1Equiv`: `J ⊗ Ȟ¹(F) ≅ Ȟ¹(F ⊗ J)` for `J`
  flat.
* `MMP.Fourfold.CurveChartDeformations.ChartSystem`: the chart system of a curve map at a point
  of a space of maps.

## Main results

* `MMP.Fourfold.CurveChartDeformations.nonempty_theory_of_chartSystem`: a chart system gives a
  two-stage obstruction theory (`MMP.Fourfold.TwoStageObstructionTheory`).

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*, Theorem 1.10 and its proof]
* Kollár, *Rational curves on algebraic varieties*, I.2 and II.1.
-/

@[expose] public section

noncomputable section

universe u

namespace MMP.Fourfold.CurveChartDeformations

open MMP.Fourfold

section ChartDeformations

open TensorProduct

/-- **The Čech data of the marked curve maps** at a point of `R`: for each small extension `E` of
`A` and each `A`-point `a`, a Čech torsor of local lifts (first stage, under the presheaf of
derivations, whose `Ȟ¹` is `V₁ ⊗ J`), and a lifting problem over the base (second stage, whose
presheaf of ideals has `Ȟ¹ = V₂ ⊗ J`) carrying the transition functions `ref` of the fixed line
bundle and `pull` of the pulled-back one for each compatible family of local lifts; both natural
in the quotients of `J`, and a compatible family whose transition functions are isomorphic over
the identity modulo `J` gives a lift of `a`. -/
structure MarkedDeformationData (k : Type u) [Field k] (R : Type u) [CommRing R]
    [Algebra k R] (ι : Type u) [DecidableEq ι] (V₁ V₂ : Type u)
    [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] where
  /-- The presheaf of derivations of the first stage for `E` and `a`. -/
  F₁ : ∀ {A : ArtinLocalAlgebra k}, SmallExtension A → (R →ₐ[k] A.carrier) → CechPresheaf.{u} k ι
  /-- The Čech torsor of local lifts of the first stage, under `F₁ E a`. -/
  T₁ : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier),
    CechTorsor (F₁ E a)
  /-- Local lifts exist on each chart. -/
  nonempty₁ : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier) (i : ι),
    Nonempty ((T₁ E a).X {i})
  /-- The morphism of presheaves of derivations induced by a quotient map of small extensions. -/
  mapF₁ : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A}, E.QuotientMap E' →
    ∀ (a : R →ₐ[k] A.carrier), (F₁ E a).Hom (F₁ E' a)
  /-- The morphism of torsors of local lifts induced by a quotient map of small extensions. -/
  mapT₁ : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A} (q : E.QuotientMap E')
    (a : R →ₐ[k] A.carrier), (T₁ E a).Hom (T₁ E' a) (mapF₁ q a)
  /-- The identification `Ȟ¹(F₁ E a) ≃ V₁ ⊗ J`. -/
  θ₁ : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier),
    (F₁ E a).H1 ≃ₗ[k] V₁ ⊗[k] E.kernel
  /-- `θ₁` is natural in the quotients of `J`. -/
  θ₁_map : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A} (q : E.QuotientMap E')
    (a : R →ₐ[k] A.carrier) (z : (F₁ E a).H1),
    θ₁ E' a ((mapF₁ q a).h1 z) = LinearMap.lTensor V₁ q.kerMap (θ₁ E a z)
  /-- The second obstruction, in `V₂ ⊗ J`, of a compatible family of local lifts. -/
  obs₂ : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier)
    (y : ∀ i : ι, (T₁ E a).X {i}),
    (∀ i j : ι, (T₁ E a).res (CechPresheaf.sub_pair_left i j) (y i) =
      (T₁ E a).res (CechPresheaf.sub_pair_right i j) (y j)) → V₂ ⊗[k] E.kernel
  /-- The second obstruction is natural in the quotients of `J`. -/
  obs₂_map : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A} (q : E.QuotientMap E')
    (a : R →ₐ[k] A.carrier) (y : ∀ i : ι, (T₁ E a).X {i}) (hy : ∀ i j : ι,
      (T₁ E a).res (CechPresheaf.sub_pair_left i j) (y i) =
        (T₁ E a).res (CechPresheaf.sub_pair_right i j) (y j))
    (hy' : ∀ i j : ι,
      (T₁ E' a).res (CechPresheaf.sub_pair_left i j) ((mapT₁ q a).map _ (y i)) =
        (T₁ E' a).res (CechPresheaf.sub_pair_right i j) ((mapT₁ q a).map _ (y j))),
    obs₂ E' a (fun i => (mapT₁ q a).map _ (y i)) hy' = LinearMap.lTensor V₂ q.kerMap (obs₂ E a y hy)
  /-- A compatible family of local lifts with vanishing second obstruction gives a lift of `a`. -/
  lift_of_obs : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier)
    (y : ∀ i : ι, (T₁ E a).X {i}) (hy : ∀ i j : ι,
      (T₁ E a).res (CechPresheaf.sub_pair_left i j) (y i) =
        (T₁ E a).res (CechPresheaf.sub_pair_right i j) (y j)),
    obs₂ E a y hy = 0 → ∃ b : R →ₐ[k] E.big.carrier, E.π.comp b = a

namespace MarkedDeformationData

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {ι : Type u}
  [DecidableEq ι] {V₁ V₂ : Type u} [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂]

/-- The image of a compatible family of local lifts under a quotient map is compatible. -/
theorem compat_map (D : MarkedDeformationData k R ι V₁ V₂) {A : ArtinLocalAlgebra k}
    {E E' : SmallExtension A} (q : E.QuotientMap E') (a : R →ₐ[k] A.carrier)
    (y : ∀ i : ι, (D.T₁ E a).X {i}) (hy : ∀ i j : ι,
      (D.T₁ E a).res (CechPresheaf.sub_pair_left i j) (y i) =
        (D.T₁ E a).res (CechPresheaf.sub_pair_right i j) (y j)) (i j : ι) :
    (D.T₁ E' a).res (CechPresheaf.sub_pair_left i j) ((D.mapT₁ q a).map _ (y i)) =
      (D.T₁ E' a).res (CechPresheaf.sub_pair_right i j) ((D.mapT₁ q a).map _ (y j)) := by
  rw [← (D.mapT₁ q a).map_res, ← (D.mapT₁ q a).map_res, hy i j]

/-- The two-stage obstruction theory of the marked deformation data. -/
def toTheory (D : MarkedDeformationData k R ι V₁ V₂) :
    TwoStageObstructionTheory.{u, u, u} k R V₁ V₂ where
  Intermediate E a := {y : ∀ i : ι, (D.T₁ E a).X {i} // ∀ i j : ι,
      (D.T₁ E a).res (CechPresheaf.sub_pair_left i j) (y i) =
        (D.T₁ E a).res (CechPresheaf.sub_pair_right i j) (y j)}
  obs₁ E a := D.θ₁ E a ((D.T₁ E a).obstruction (fun i => (D.nonempty₁ E a i).some))
  obs₂ {_} {E} {a} y := D.obs₂ E a y.1 y.2
  exists_intermediate E a h := by
    have h0 : (D.T₁ E a).obstruction (fun i => (D.nonempty₁ E a i).some) = 0 :=
      (D.θ₁ E a).injective (by rwa [map_zero])
    obtain ⟨y, hy⟩ := ((D.T₁ E a).obstruction_eq_zero_iff _).1 h0
    exact ⟨⟨y, hy⟩⟩
  exists_lift E a y h := D.lift_of_obs E a y.1 y.2 h
  mapIntermediate := fun {A} {E} {E'} q {a} y =>
    ⟨fun i => (D.mapT₁ q a).map _ (y.1 i), D.compat_map q a y.1 y.2⟩
  obs₁_map q a := by
    rw [← D.θ₁_map q a, (D.mapT₁ q a).obstruction_map]
    exact congrArg _ (CechTorsor.obstruction_eq _ _ _)
  obs₂_map := fun {A} {E} {E'} q {a} y => D.obs₂_map q a y.1 y.2 _

end MarkedDeformationData

section NChart

/-- **Target charts on the nonempty intersections** of a finite cover: smooth affine charts
`Spec (S s)` of the target for the nonempty `s`, with formally étale restriction maps. -/
structure NChartData (k : Type u) [Field k] (ι : Type u) where
  /-- The ring of the target chart over the intersection `s`. -/
  S : Finset ι → Type u
  [cr : ∀ s, CommRing (S s)]
  [alg : ∀ s, Algebra k (S s)]
  /-- The restriction map `S s → S t` for `s ⊆ t`. -/
  σ : ∀ {s t : Finset ι}, s ⊆ t → S s →ₐ[k] S t
  /-- Restriction along `s ⊆ s` is the identity. -/
  σ_refl : ∀ {s : Finset ι} (h : s ⊆ s) (x : S s), σ h x = x
  /-- Restriction is transitive. -/
  σ_comp : ∀ {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (x : S s),
    σ h₂ (σ h₁ x) = σ (h₁.trans h₂) x
  /-- `S s` is formally smooth over `k` for nonempty `s`. -/
  smooth : ∀ s : Finset ι, s.Nonempty → Algebra.FormallySmooth k (S s)
  /-- The restriction `S s → S t` is formally étale for nonempty `s`. -/
  etale : ∀ {s t : Finset ι} (h : s ⊆ t), s.Nonempty → (σ h).toRingHom.FormallyEtale

attribute [instance] NChartData.cr NChartData.alg

/-- **A lifting problem over the nonempty intersections**: rings `P s` with square-zero ideals
`I s`, maps `φ s : S s → P s / I s` for nonempty `s`, and restriction maps compatible with the
charts. -/
structure NLiftCover {k : Type u} [Field k] {ι : Type u} (W : NChartData k ι) where
  /-- The thickened ring over the intersection `s`. -/
  P : Finset ι → Type u
  [cr : ∀ s, CommRing (P s)]
  [alg : ∀ s, Algebra k (P s)]
  /-- The ideal of `P s` along which the maps are lifted. -/
  I : ∀ s, Ideal (P s)
  /-- `I s` is square-zero. -/
  hI : ∀ s, I s * I s = ⊥
  /-- The map `S s → P s / I s` to be lifted, for nonempty `s`. -/
  φ : ∀ s, s.Nonempty → (W.S s →ₐ[k] P s ⧸ I s)
  /-- The restriction map `P s → P t` for `s ⊆ t`. -/
  ψ : ∀ {s t : Finset ι}, s ⊆ t → P s →ₐ[k] P t
  /-- Restriction along `s ⊆ s` is the identity. -/
  ψ_refl : ∀ {s : Finset ι} (h : s ⊆ s) (x : P s), ψ h x = x
  /-- Restriction is transitive. -/
  ψ_comp : ∀ {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (x : P s),
    ψ h₂ (ψ h₁ x) = ψ (h₁.trans h₂) x
  /-- Restriction maps `I s` into `I t`. -/
  mem : ∀ {s t : Finset ι} (h : s ⊆ t) (x : P s), x ∈ I s → ψ h x ∈ I t
  /-- Restriction is compatible with the maps `φ` and the chart restrictions `σ`. -/
  compat : ∀ {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty) (a : W.S s) (p : P s),
    Ideal.Quotient.mk (I s) p = φ s hs a →
      Ideal.Quotient.mk (I t) (ψ h p) = φ t (hs.mono h) (W.σ h a)

attribute [instance] NLiftCover.cr NLiftCover.alg

namespace NLiftCover

variable {k : Type u} [Field k] {ι : Type u} [DecidableEq ι] {W : NChartData k ι}
  (C : NLiftCover W)

/-- The restriction as a morphism of thickening problems. -/
def hom {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty) :
    ChartHom (W.σ h) (C.I s) (C.φ s hs) (C.I t) (C.φ t (hs.mono h)) :=
  ⟨C.ψ h, C.mem h, C.compat h hs⟩

/-- Extending a derivation along `s ⊆ s` is the identity. -/
theorem extDeriv_refl {s : Finset ι} (h : s ⊆ s) (hs : s.Nonempty)
    (x : Deriv (C.I s) (C.φ s hs)) :
    haveI := W.smooth s hs
    (C.hom h hs).extDeriv (W.etale h hs) (C.hI s) (C.hI s) x = x := by
  haveI := W.smooth s hs
  exact ((C.hom h hs).extDeriv_unique (W.etale h hs) (C.hI s) (C.hI s) x x
    (fun a => by rw [W.σ_refl]; exact (C.ψ_refl h _).symm)).symm

/-- Extension of derivations along `s ⊆ t ⊆ u` is the composite of the two extensions. -/
theorem extDeriv_comp {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (hs : s.Nonempty)
    (x : Deriv (C.I s) (C.φ s hs)) :
    haveI := W.smooth s hs
    haveI := W.smooth t (hs.mono h₁)
    (C.hom h₂ (hs.mono h₁)).extDeriv (W.etale h₂ (hs.mono h₁)) (C.hI t) (C.hI u)
      ((C.hom h₁ hs).extDeriv (W.etale h₁ hs) (C.hI s) (C.hI t) x) =
    (C.hom (h₁.trans h₂) hs).extDeriv (W.etale (h₁.trans h₂) hs) (C.hI s) (C.hI u) x := by
  haveI := W.smooth s hs
  haveI := W.smooth t (hs.mono h₁)
  refine (C.hom (h₁.trans h₂) hs).extDeriv_unique (W.etale (h₁.trans h₂) hs) (C.hI s)
    (C.hI u) x _ (fun a => ?_)
  rw [← W.σ_comp h₁ h₂, ChartHom.extDeriv_apply, ChartHom.extDeriv_apply]
  exact C.ψ_comp h₁ h₂ _

/-- Extending a lift along `s ⊆ s` is the identity. -/
theorem extLift_refl {s : Finset ι} (h : s ⊆ s) (hs : s.Nonempty)
    (x : LiftsOf (C.I s) (C.φ s hs)) :
    (C.hom h hs).extLift (W.etale h hs) (C.hI s) x = x :=
  ((C.hom h hs).extLift_unique (W.etale h hs) (C.hI s) x x
    (fun a => by rw [W.σ_refl]; exact (C.ψ_refl h _).symm)).symm

/-- Extension of lifts along `s ⊆ t ⊆ u` is the composite of the two extensions. -/
theorem extLift_comp {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (hs : s.Nonempty)
    (x : LiftsOf (C.I s) (C.φ s hs)) :
    (C.hom h₂ (hs.mono h₁)).extLift (W.etale h₂ (hs.mono h₁)) (C.hI u)
      ((C.hom h₁ hs).extLift (W.etale h₁ hs) (C.hI t) x) =
    (C.hom (h₁.trans h₂) hs).extLift (W.etale (h₁.trans h₂) hs) (C.hI u) x := by
  refine (C.hom (h₁.trans h₂) hs).extLift_unique (W.etale (h₁.trans h₂) hs) (C.hI u)
    x _ (fun a => ?_)
  rw [← W.σ_comp h₁ h₂, ChartHom.extLift_apply, ChartHom.extLift_apply]
  exact C.ψ_comp h₁ h₂ _

/-- The restriction of derivations (zero out of the empty intersection). -/
def derivRes {s t : Finset ι} (h : s ⊆ t) :
    (∀ hs : PLift s.Nonempty, Deriv (C.I s) (C.φ s hs.down)) →ₗ[k]
      (∀ ht : PLift t.Nonempty, Deriv (C.I t) (C.φ t ht.down)) where
  toFun D ht := if hs : s.Nonempty then
      haveI := W.smooth s hs
      (C.hom h hs).extDerivₗ (W.etale h hs) (C.hI s) (C.hI t) (D ⟨hs⟩) else 0
  map_add' D E := by
    funext ht
    by_cases hs : s.Nonempty
    · simp only [dif_pos hs, Pi.add_apply, map_add]
    · simp only [dif_neg hs, Pi.add_apply, add_zero]
  map_smul' c D := by
    funext ht
    by_cases hs : s.Nonempty
    · simp only [dif_pos hs, Pi.smul_apply, map_smul, RingHom.id_apply]
    · simp only [dif_neg hs, Pi.smul_apply, smul_zero, RingHom.id_apply]

/-- On a nonempty `s`, `derivRes` is the extension of derivations along `S s → S t`. -/
theorem derivRes_apply {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty)
    (D : ∀ hs : PLift s.Nonempty, Deriv (C.I s) (C.φ s hs.down)) (ht : PLift t.Nonempty) :
    haveI := W.smooth s hs
    C.derivRes h D ht = (C.hom h hs).extDeriv (W.etale h hs) (C.hI s) (C.hI t) (D ⟨hs⟩) := by
  simp only [derivRes, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hs]
  rfl

/-- **The presheaf of derivations** `s ↦ Der(S_s, I_s)` along `φ_s` (zero on `∅`). -/
def derivPresheaf : CechPresheaf.{u} k ι where
  obj s := ∀ hs : PLift s.Nonempty, Deriv (C.I s) (C.φ s hs.down)
  res h := C.derivRes h
  res_refl {s} h x := by
    funext hs
    rw [C.derivRes_apply h hs.down]
    exact C.extDeriv_refl h hs.down (x hs)
  res_comp {s t u} h₁ h₂ x := by
    funext hu
    by_cases hs : s.Nonempty
    · rw [C.derivRes_apply _ (hs.mono h₁), C.derivRes_apply _ hs, C.derivRes_apply _ hs]
      exact C.extDeriv_comp h₁ h₂ hs (x ⟨hs⟩)
    · have e1 : C.derivRes (h₁.trans h₂) x hu = 0 := by
        simp only [derivRes, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hs]
      have e2 : C.derivRes h₁ x = 0 := by
        funext ht; simp only [derivRes, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hs]; rfl
      rw [e1, e2, map_zero]; rfl

/-- **The pseudo-torsor of local lifts** (empty over `∅`). -/
def liftTorsor : CechTorsor C.derivPresheaf where
  X s := (hs : s.Nonempty) ×' LiftsOf (C.I s) (C.φ s hs)
  res h x := ⟨x.1.mono h, (C.hom h x.1).extLift (W.etale h x.1) (C.hI _) x.2⟩
  res_refl h x := by
    obtain ⟨hs, g⟩ := x
    exact PSigma.ext rfl (heq_of_eq (C.extLift_refl h hs g))
  res_comp h₁ h₂ x := by
    obtain ⟨hs, g⟩ := x
    exact PSigma.ext rfl (heq_of_eq (C.extLift_comp h₁ h₂ hs g))
  vadd s D x := ⟨x.1, x.2.add (C.hI s) (D ⟨x.1⟩)⟩
  vsub s x y := fun hs => x.2.sub (C.hI s) y.2
  vadd_zero s x := PSigma.ext rfl (heq_of_eq (x.2.add_zero (C.hI s)))
  vadd_add s D E x := by
    refine PSigma.ext rfl (heq_of_eq ?_)
    have := LiftsOf.add_add (C.hI s) x.2 (E ⟨x.1⟩) (D ⟨x.1⟩)
    exact (congrArg (LiftsOf.add (C.hI s) x.2) (add_comm (D ⟨x.1⟩) (E ⟨x.1⟩))).trans this.symm
  vsub_vadd s x y := by
    obtain ⟨hs, g⟩ := x
    obtain ⟨hs', g'⟩ := y
    exact PSigma.ext rfl (heq_of_eq (LiftsOf.sub_add_cancel (C.hI s) g g'))
  vadd_vsub s D y := by
    funext hs
    exact LiftsOf.add_sub_cancel (C.hI s) y.2 (D ⟨y.1⟩)
  res_vadd h D x := by
    obtain ⟨hs, g⟩ := x
    refine PSigma.ext rfl (heq_of_eq ?_)
    haveI := W.smooth _ hs
    change (C.hom h hs).extLift (W.etale h hs) (C.hI _) (g.add (C.hI _) (D ⟨hs⟩)) =
      ((C.hom h hs).extLift (W.etale h hs) (C.hI _) g).add (C.hI _) (C.derivRes h D ⟨hs.mono h⟩)
    have key : C.derivRes h D ⟨hs.mono h⟩ =
        (C.hom h hs).extDeriv (W.etale h hs) (C.hI _) (C.hI _) (D ⟨hs⟩) :=
      C.derivRes_apply h hs D _
    rw [key]
    exact (C.hom h hs).extLift_add (W.etale h hs) (C.hI _) (C.hI _) g (D ⟨hs⟩)

omit [DecidableEq ι] in
/-- Local lifts exist on each chart. -/
theorem nonempty_X [DecidableEq ι] (i : ι) : Nonempty (C.liftTorsor.X {i}) := by
  haveI := W.smooth {i} (Finset.singleton_nonempty i)
  exact ⟨⟨Finset.singleton_nonempty i, (LiftsOf.nonempty (C.hI _) _).some⟩⟩

/-- A morphism of lifting problems over the same charts (a quotient of the extension). -/
structure Hom (C C' : NLiftCover W) where
  /-- The map of thickened rings on the intersection `s`. -/
  sq : ∀ s, C.P s →ₐ[k] C'.P s
  /-- `sq s` maps `C.I s` into `C'.I s`. -/
  mem : ∀ s (x : C.P s), x ∈ C.I s → sq s x ∈ C'.I s
  /-- `sq s` is compatible with the maps to be lifted. -/
  compat : ∀ s (hs : s.Nonempty) (a : W.S s) (p : C.P s),
    Ideal.Quotient.mk (C.I s) p = C.φ s hs a → Ideal.Quotient.mk (C'.I s) (sq s p) = C'.φ s hs a
  /-- `sq` commutes with restriction. -/
  comm : ∀ {s t : Finset ι} (h : s ⊆ t) (x : C.P s), sq t (C.ψ h x) = C'.ψ h (sq s x)

variable {C} {C' : NLiftCover W} (m : Hom C C')

/-- The square-zero morphism of a morphism of lift covers on the intersection `s`. -/
def Hom.sqHom (s : Finset ι) (hs : s.Nonempty) :
    SqZeroHom (C.I s) (C.φ s hs) (C'.I s) (C'.φ s hs) :=
  ⟨m.sq s, m.mem s, m.compat s hs⟩

/-- The induced morphism of presheaves of derivations. -/
def Hom.derivHom : C.derivPresheaf.Hom C'.derivPresheaf where
  map s :=
    { toFun := fun D hs => (m.sqHom s hs.down).mapDerivₗ (C'.hI s) (D hs)
      map_add' := fun D E => by funext hs; exact LinearMap.map_add _ (D hs) (E hs)
      map_smul' := fun c D => by funext hs; exact LinearMap.map_smul _ c (D hs) }
  map_res {s t} h x := by
    funext ht
    have hx : C.derivPresheaf.obj s = ∀ hs : PLift s.Nonempty, Deriv (C.I s) (C.φ s hs.down) := rfl
    obtain ⟨x, rfl⟩ : ∃ x' : ∀ hs : PLift s.Nonempty, Deriv (C.I s) (C.φ s hs.down), x' = x :=
      ⟨x, rfl⟩
    by_cases hs : s.Nonempty
    · haveI := W.smooth s hs
      change (m.sqHom t ht.down).mapDerivₗ (C'.hI t) (C.derivRes h x ht) =
        C'.derivRes h (fun hs => (m.sqHom s hs.down).mapDerivₗ (C'.hI s) (x hs)) ht
      rw [C.derivRes_apply h hs, C'.derivRes_apply h hs]
      refine (C'.hom h hs).extDeriv_unique (W.etale h hs) (C'.hI s) (C'.hI t) _ _ (fun a => ?_)
      have e := (C.hom h hs).extDeriv_apply (W.etale h hs) (C.hI s) (C.hI t) (x ⟨hs⟩) a
      change m.sq t ((((C.hom h hs).extDeriv (W.etale h hs) (C.hI s) (C.hI t) (x ⟨hs⟩)).1
        (W.σ h a) : C.I t) : C.P t) = _
      rw [e]
      exact m.comm h _
    · have e1 : C.derivRes h x ht = 0 := by
        simp only [derivRes, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hs]
      change (m.sqHom t ht.down).mapDerivₗ (C'.hI t) (C.derivRes h x ht) =
        C'.derivRes h _ ht
      rw [e1, map_zero]
      simp only [derivRes, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hs]

/-- The induced morphism of torsors of local lifts. -/
def Hom.liftHom : C.liftTorsor.Hom C'.liftTorsor m.derivHom where
  map s x := ⟨x.1, (m.sqHom s x.1).mapLift x.2⟩
  map_res {s t} h x := by
    obtain ⟨hs, g⟩ := x
    refine PSigma.ext rfl (heq_of_eq ?_)
    refine (C'.hom h hs).extLift_unique (W.etale h hs) (C'.hI t) _ _ (fun a => ?_)
    have e := (C.hom h hs).extLift_apply (W.etale h hs) (C.hI t) g a
    change m.sq t (((C.hom h hs).extLift (W.etale h hs) (C.hI t) g).1 (W.σ h a)) = _
    rw [e]
    exact m.comm h _
  map_vadd s D x := PSigma.ext rfl (heq_of_eq
    ((m.sqHom s x.1).mapLift_add (C.hI s) (C'.hI s) x.2 (D ⟨x.1⟩)))

end NLiftCover

end NChart

section Residue

variable {k : Type u} [Field k]

/-- The residue map `A → k` of a local Artinian `k`-algebra with residue field `k`. -/
def toRes (A : ArtinLocalAlgebra k) : A.carrier →ₐ[k] k :=
  letI e : k ≃+* IsLocalRing.ResidueField A.carrier :=
    RingEquiv.ofBijective (algebraMap k (IsLocalRing.ResidueField A.carrier)) A.residue_bijective
  { toRingHom := e.symm.toRingHom.comp (IsLocalRing.residue A.carrier)
    commutes' := fun x => by
      change e.symm (IsLocalRing.residue A.carrier (algebraMap k A.carrier x)) = x
      have : IsLocalRing.residue A.carrier (algebraMap k A.carrier x) = e x := rfl
      rw [this, RingEquiv.symm_apply_apply] }

/-- The kernel of a `k`-algebra map from a local `k`-algebra to `k` is the maximal ideal. -/
theorem ker_algHom_eq_maximalIdeal' {R : Type*} [CommRing R] [IsLocalRing R]
    [Algebra k R] (ε : R →ₐ[k] k) : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal R :=
  IsLocalRing.ker_eq_maximalIdeal _ fun x => ⟨algebraMap k R x, ε.commutes x⟩

/-- A local `k`-algebra has at most one `k`-algebra map to `k`. -/
theorem algHom_eq_of_local' {R : Type*} [CommRing R] [IsLocalRing R] [Algebra k R]
    (φ ψ : R →ₐ[k] k) : φ = ψ := by
  ext r
  have h1 : r - algebraMap k R (φ r) ∈ RingHom.ker ψ.toRingHom := by
    rw [ker_algHom_eq_maximalIdeal' ψ, ← ker_algHom_eq_maximalIdeal' φ]
    change φ (r - algebraMap k R (φ r)) = 0
    rw [map_sub, φ.commutes]
    simp
  have h2 : ψ (r - algebraMap k R (φ r)) = 0 := h1
  rw [map_sub, ψ.commutes, sub_eq_zero] at h2
  exact h2.symm

/-- The residue map is compatible with `k`-algebra maps of local Artinian algebras. -/
theorem toRes_comp {A A' : ArtinLocalAlgebra k} (π : A'.carrier →ₐ[k] A.carrier) :
    (toRes A).comp π = toRes A' :=
  algHom_eq_of_local' _ _

/-- The kernel of a small extension is finite-dimensional: it is a finitely generated ideal killed
by the maximal ideal. -/
theorem finite_kernel {A : ArtinLocalAlgebra k} (E : SmallExtension A) :
    Module.Finite k E.kernel := by
  classical
  haveI : IsNoetherianRing E.big.carrier := inferInstance
  have hfg : (RingHom.ker E.π.toRingHom).FG := IsNoetherian.noetherian _
  obtain ⟨T, hT⟩ := hfg
  have hmem : ∀ {x}, x ∈ Ideal.span (T : Set E.big.carrier) → x ∈ E.kernel := fun {x} hx =>
    (hT ▸ Ideal.span_le.2 (fun t ht => hT ▸ Ideal.subset_span ht) hx :
      x ∈ RingHom.ker E.π.toRingHom)
  refine ⟨⟨T.attach.image (fun x => (⟨x.1,
    (hT ▸ Ideal.subset_span x.2 : x.1 ∈ RingHom.ker E.π.toRingHom)⟩ : E.kernel)), ?_⟩⟩
  rw [eq_top_iff]
  rintro ⟨y, hy⟩ -
  have hy' : y ∈ Ideal.span (T : Set E.big.carrier) := by rwa [hT]
  rw [Finset.coe_image]
  refine Submodule.span_induction (p := fun y _ => ∀ hy : y ∈ E.kernel,
      (⟨y, hy⟩ : E.kernel) ∈ Submodule.span k _) ?_ ?_ ?_ ?_ hy' hy
  · intro x hx hxk
    exact Submodule.subset_span ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
  · exact fun _ => (Submodule.span k _).zero_mem
  · intro x z hx hz ihx ihz hxz
    exact (Submodule.span k _).add_mem (ihx (hmem hx)) (ihz (hmem hz))
  · intro b x hx ih hbx
    have hx' : x ∈ E.kernel := hmem hx
    set c := toRes E.big b
    have hm : b - algebraMap k _ c ∈ IsLocalRing.maximalIdeal E.big.carrier := by
      rw [← ker_algHom_eq_maximalIdeal' (toRes E.big)]
      change toRes E.big (b - algebraMap k _ c) = 0
      rw [map_sub, AlgHom.commutes]
      simp [c]
    have hz : (b - algebraMap k _ c) * x = 0 := by
      have : x * (b - algebraMap k _ c) ∈ RingHom.ker E.π.toRingHom * IsLocalRing.maximalIdeal _ :=
        Ideal.mul_mem_mul hx' hm
      have e : RingHom.ker E.π.toRingHom * IsLocalRing.maximalIdeal E.big.carrier = ⊥ :=
        E.ker_mul_maximalIdeal
      rw [e, Ideal.mem_bot] at this
      rwa [mul_comm]
    have hbx' : (⟨b • x, hbx⟩ : E.kernel) = c • ⟨x, hx'⟩ := by
      apply Subtype.ext
      change b * x = c • x
      rw [Algebra.smul_def]
      linear_combination hz
    rw [hbx']
    exact (Submodule.span k _).smul_mem c (ih hx')

end Residue

section TensorKernels

open TensorProduct

variable {k : Type u} [Field k] {M O O' J B A : Type u} [AddCommGroup M] [Module k M]
  [AddCommGroup O] [Module k O] [AddCommGroup O'] [Module k O'] [AddCommGroup J] [Module k J]
  [AddCommGroup B] [Module k B] [AddCommGroup A] [Module k A]
  {ι : M →ₗ[k] O} {p : O →ₗ[k] O'} {j : J →ₗ[k] B} {π : B →ₗ[k] A}

/-- **The intersection of the two kernels of `O ⊗ B` is the image of `M ⊗ J`**, for exact
sequences `M → O → O'` and `J → B → A` of vector spaces with surjective second maps. -/
theorem mem_range_map_iff (hι : Function.Exact ι p) (hp : Function.Surjective p)
    (hj : Function.Exact j π) (hπ : Function.Surjective π) (hjinj : Function.Injective j)
    (x : O ⊗[k] B) :
    x ∈ LinearMap.range (TensorProduct.map ι j) ↔
      LinearMap.lTensor O π x = 0 ∧ LinearMap.rTensor B p x = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_map]
      have : π ∘ₗ j = 0 := LinearMap.ext hj.apply_apply_eq_zero
      rw [this, TensorProduct.map_zero_right, LinearMap.zero_apply]
    · rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_map]
      have : p ∘ₗ ι = 0 := LinearMap.ext hι.apply_apply_eq_zero
      rw [this, TensorProduct.map_zero_left, LinearMap.zero_apply]
  · rintro ⟨h1, h2⟩
    obtain ⟨z, rfl⟩ := ((lTensor_exact O hj hπ) x).1 h1
    have h3 : LinearMap.lTensor O' j (LinearMap.rTensor J p z) = 0 := by
      rw [← h2, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor]
    have h4 : LinearMap.rTensor J p z = 0 :=
      Module.Flat.lTensor_preserves_injective_linearMap j hjinj (by rw [h3, map_zero])
    obtain ⟨w, rfl⟩ := ((rTensor_exact J hι hp) z).1 h4
    refine ⟨w, ?_⟩
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]

end TensorKernels

section AlgTensor

variable {k : Type u} [Field k] {X Y Z : Type u} [CommRing X] [Algebra k X] [CommRing Y]
  [Algebra k Y] [CommRing Z] [Algebra k Z]

/-- `id ⊗ g` as an algebra map agrees with `LinearMap.lTensor X g`. -/
theorem algMap_id_apply (g : Y →ₐ[k] Z) (x : X ⊗[k] Y) :
    Algebra.TensorProduct.map (AlgHom.id k X) g x = LinearMap.lTensor X g.toLinearMap x :=
  rfl

/-- `g ⊗ id` as an algebra map agrees with `LinearMap.rTensor Y g`. -/
theorem algMap_left_apply (g : X →ₐ[k] Z) (x : X ⊗[k] Y) :
    Algebra.TensorProduct.map g (AlgHom.id k Y) x = LinearMap.rTensor Y g.toLinearMap x :=
  rfl

end AlgTensor

section EtaleDerivation

variable {k S S' N' : Type*} [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra k S']
  [AddCommGroup N'] [Module k N'] [Module S' N'] [IsScalarTower k S' N']

/-- **Derivations extend uniquely along formally étale maps.** -/
theorem existsUnique_derivation_etale (σ : S →ₐ[k] S') (hσ : σ.toRingHom.FormallyEtale)
    (δ : S →ₗ[k] N') (hδ : ∀ a b, δ (a * b) = σ a • δ b + σ b • δ a) :
    ∃! D : Derivation k S' N', ∀ a, D (σ a) = δ a := by
  letI : Algebra S S' := σ.toRingHom.toAlgebra
  haveI : Algebra.FormallyEtale S S' := hσ
  haveI : IsScalarTower k S S' := IsScalarTower.of_algebraMap_eq fun r => (σ.commutes r).symm
  letI : Module S N' := Module.compHom N' σ.toRingHom
  haveI : IsScalarTower S S' N' := ⟨fun a x m => mul_smul (σ a) x m⟩
  haveI : IsScalarTower k S N' := ⟨fun r a m => by
    change σ (r • a) • m = r • (σ a • m)
    rw [map_smul, smul_assoc]⟩
  let δD : Derivation k S N' :=
    { toLinearMap := δ
      map_one_eq_zero' := by
        simpa using hδ 1 1
      leibniz' := fun a b => hδ a b }
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale k S S'
  have key : ∀ D : Derivation k S' N', (∀ a, D (σ a) = δ a) ↔
      (D.liftKaehlerDifferential.restrictScalars S).comp (KaehlerDifferential.map k k S S') =
        δD.liftKaehlerDifferential := by
    intro D
    constructor
    · intro h
      apply (KaehlerDifferential.linearMapEquivDerivation k S).injective
      refine Derivation.ext fun a => ?_
      simp only [KaehlerDifferential.linearMapEquivDerivation_apply_apply, LinearMap.comp_apply,
        LinearMap.coe_restrictScalars]
      rw [KaehlerDifferential.map_D k k S S' a, Derivation.liftKaehlerDifferential_comp_D,
        Derivation.liftKaehlerDifferential_comp_D]
      exact h a
    · intro h a
      have := LinearMap.congr_fun h (KaehlerDifferential.D k S a)
      simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars] at this
      rwa [KaehlerDifferential.map_D k k S S' a, Derivation.liftKaehlerDifferential_comp_D,
        Derivation.liftKaehlerDifferential_comp_D] at this
  refine ⟨KaehlerDifferential.linearMapEquivDerivation k S' (hb.lift δD.liftKaehlerDifferential),
    (key _).2 ?_, fun D hD => ?_⟩
  · have : (KaehlerDifferential.linearMapEquivDerivation k S'
        (hb.lift δD.liftKaehlerDifferential)).liftKaehlerDifferential =
        hb.lift δD.liftKaehlerDifferential :=
      (KaehlerDifferential.linearMapEquivDerivation k S').symm_apply_apply _
    rw [this]
    exact hb.lift_comp _
  · have h1 := (key D).1 hD
    have h2 : D.liftKaehlerDifferential = hb.lift δD.liftKaehlerDifferential :=
      hb.algHom_ext' _ _ (h1.trans (hb.lift_comp _).symm)
    exact ((KaehlerDifferential.linearMapEquivDerivation k S').apply_symm_apply D).symm.trans
      (congrArg (KaehlerDifferential.linearMapEquivDerivation k S') h2)

end EtaleDerivation

section Charts

open TensorProduct

/-- **The charts of a curve map**: target charts `S s` (smooth, formally étale restrictions on the
nonempty intersections), the rings `O s` of the source charts with restriction maps, the ideals
`𝔟 s` of the marked points, and the map `f0 s : S s → O s` of the given curve map. -/
structure CurveCharts (k : Type u) [Field k] (ι : Type u) extends NChartData k ι where
  /-- The ring of the source chart over the intersection `s`. -/
  O : Finset ι → Type u
  [crO : ∀ s, CommRing (O s)]
  [algO : ∀ s, Algebra k (O s)]
  /-- The restriction map `O s → O t` for `s ⊆ t`. -/
  ρ : ∀ {s t : Finset ι}, s ⊆ t → O s →ₐ[k] O t
  /-- Restriction along `s ⊆ s` is the identity. -/
  ρ_refl : ∀ {s : Finset ι} (h : s ⊆ s) (x : O s), ρ h x = x
  /-- Restriction is transitive. -/
  ρ_comp : ∀ {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (x : O s),
    ρ h₂ (ρ h₁ x) = ρ (h₁.trans h₂) x
  /-- The ideal of the marked points in `O s`. -/
  𝔟 : ∀ s, Ideal (O s)
  /-- Restriction maps `𝔟 s` into `𝔟 t`. -/
  ρ_mem : ∀ {s t : Finset ι} (h : s ⊆ t) (x : O s), x ∈ 𝔟 s → ρ h x ∈ 𝔟 t
  /-- The given curve map on the chart `s`. -/
  f0 : ∀ s, S s →ₐ[k] O s
  /-- `f0` commutes with restriction. -/
  f0_comm : ∀ {s t : Finset ι} (h : s ⊆ t) (x : S s), f0 t (σ h x) = ρ h (f0 s x)

attribute [instance] CurveCharts.crO CurveCharts.algO

namespace CurveCharts

variable {k : Type u} [Field k] {ι : Type u} (Ch : CurveCharts k ι)

/-- `S s` acts on the ideal `𝔟 s` through `f0 s`. -/
instance moduleB (s : Finset ι) : Module (Ch.S s) (Ch.𝔟 s) :=
  Module.compHom _ (Ch.f0 s).toRingHom

/-- `a • n` in `𝔟 s` is `f0 s a * n` in `O s`. -/
theorem coe_smulB {s : Finset ι} (a : Ch.S s) (n : Ch.𝔟 s) :
    ((a • n : Ch.𝔟 s) : Ch.O s) = Ch.f0 s a * n := rfl

/-- `𝔟_s` is a scalar tower over `k → S_s`. -/
instance towerB (s : Finset ι) : IsScalarTower k (Ch.S s) (Ch.𝔟 s) :=
  ⟨fun r a n => by
    apply Subtype.ext
    change Ch.f0 s (r • a) * (n : Ch.O s) = r • (Ch.f0 s a * n)
    rw [map_smul, smul_mul_assoc]⟩

/-- Restriction of sections of `𝔟`. -/
def ρB {s t : Finset ι} (h : s ⊆ t) : Ch.𝔟 s →ₗ[k] Ch.𝔟 t where
  toFun n := ⟨Ch.ρ h n, Ch.ρ_mem h n n.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_smul (Ch.ρ h) c (x : Ch.O s))

/-- `ρB h n` is `ρ h n` in `O t`. -/
theorem coe_ρB {s t : Finset ι} (h : s ⊆ t) (n : Ch.𝔟 s) :
    ((Ch.ρB h n : Ch.𝔟 t) : Ch.O t) = Ch.ρ h n := rfl

/-- `ρB h` is semilinear along `σ h`. -/
theorem ρB_smul {s t : Finset ι} (h : s ⊆ t) (a : Ch.S s) (n : Ch.𝔟 s) :
    Ch.ρB h (a • n) = Ch.σ h a • Ch.ρB h n := by
  apply Subtype.ext
  rw [coe_ρB, coe_smulB, coe_smulB, coe_ρB, map_mul, Ch.f0_comm]

/-- A derivation `S_s → 𝔟_s` extends uniquely to a derivation `S_t → 𝔟_t` compatible with
`σ h` and `ρB h`. -/
theorem existsUnique_extDerB {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty)
    (D : Derivation k (Ch.S s) (Ch.𝔟 s)) :
    ∃! D' : Derivation k (Ch.S t) (Ch.𝔟 t), ∀ a, D' (Ch.σ h a) = Ch.ρB h (D a) :=
  existsUnique_derivation_etale (Ch.σ h) (Ch.etale h hs) (Ch.ρB h ∘ₗ D.toLinearMap) (fun a b => by
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe, Derivation.leibniz, map_add,
      Ch.ρB_smul])

/-- The unique extension of a derivation `S_s → 𝔟_s` along the étale map `S_s → S_t`,
compatible with the restriction `𝔟_s → 𝔟_t`. -/
def extDerB {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty)
    (D : Derivation k (Ch.S s) (Ch.𝔟 s)) : Derivation k (Ch.S t) (Ch.𝔟 t) :=
  (Ch.existsUnique_extDerB h hs D).exists.choose

/-- `extDerB h hs D` agrees with `ρB h ∘ D` on the image of `σ h`. -/
theorem extDerB_apply {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty)
    (D : Derivation k (Ch.S s) (Ch.𝔟 s)) (a : Ch.S s) :
    Ch.extDerB h hs D (Ch.σ h a) = Ch.ρB h (D a) :=
  (Ch.existsUnique_extDerB h hs D).exists.choose_spec a

/-- A derivation agreeing with `ρB h ∘ D` on the image of `σ h` is `extDerB h hs D`. -/
theorem extDerB_unique {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty)
    (D : Derivation k (Ch.S s) (Ch.𝔟 s)) (D' : Derivation k (Ch.S t) (Ch.𝔟 t))
    (hD' : ∀ a, D' (Ch.σ h a) = Ch.ρB h (D a)) : D' = Ch.extDerB h hs D :=
  (Ch.existsUnique_extDerB h hs D).unique hD' (Ch.extDerB_apply h hs D)

/-- The extension of derivations along `S_s → S_t`, as a `k`-linear map. -/
def extDerBₗ {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty) :
    Derivation k (Ch.S s) (Ch.𝔟 s) →ₗ[k] Derivation k (Ch.S t) (Ch.𝔟 t) where
  toFun := Ch.extDerB h hs
  map_add' D E := (Ch.extDerB_unique h hs (D + E) (Ch.extDerB h hs D + Ch.extDerB h hs E)
    (fun a => by simp [extDerB_apply])).symm
  map_smul' c D := (Ch.extDerB_unique h hs (c • D) (c • Ch.extDerB h hs D) (fun a => by
    simp [extDerB_apply])).symm

/-- **The presheaf of derivations `Der_k(S_s, 𝔟_s)`** on the nerve (zero on `∅`): in the
application, the sections of `f^*T_U(-B)` over the intersections of the cover. -/
def derivPresheafB : CechPresheaf.{u} k ι where
  obj s := ∀ _ : PLift s.Nonempty, Derivation k (Ch.S s) (Ch.𝔟 s)
  res {s t} h :=
    { toFun := fun D ht => if hs : s.Nonempty then Ch.extDerBₗ h hs (D ⟨hs⟩) else 0
      map_add' := fun D E => by
        funext ht
        by_cases hs : s.Nonempty
        · simp only [dif_pos hs, Pi.add_apply, map_add]
        · simp only [dif_neg hs, Pi.add_apply, add_zero]
      map_smul' := fun c D => by
        funext ht
        by_cases hs : s.Nonempty
        · simp only [dif_pos hs, Pi.smul_apply, map_smul, RingHom.id_apply]
        · simp only [dif_neg hs, Pi.smul_apply, smul_zero, RingHom.id_apply] }
  res_refl {s} h x := by
    funext hs
    simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hs.down]
    exact (Ch.extDerB_unique h hs.down (x ⟨hs.down⟩) (x ⟨hs.down⟩) (fun a => by
      rw [Ch.σ_refl]; exact Subtype.ext (Ch.ρ_refl h _).symm)).symm
  res_comp {s t u} h₁ h₂ x := by
    funext hu
    by_cases hs : s.Nonempty
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hs, dif_pos (hs.mono h₁)]
      refine Ch.extDerB_unique (h₁.trans h₂) hs _ _ (fun a => ?_)
      rw [← Ch.σ_comp h₁ h₂]
      change Ch.extDerB h₂ (hs.mono h₁) (Ch.extDerB h₁ hs (x ⟨hs⟩)) (Ch.σ h₂ (Ch.σ h₁ a)) = _
      rw [extDerB_apply, extDerB_apply]
      exact Subtype.ext (Ch.ρ_comp h₁ h₂ _)
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_neg hs]
      by_cases ht : t.Nonempty
      · simp only [dif_pos ht, map_zero]
      · simp only [dif_neg ht]

/-- **The presheaf of rings of the source charts**, as `k`-modules. -/
def ringPresheaf : CechPresheaf.{u} k ι where
  obj s := Ch.O s
  res h := (Ch.ρ h).toLinearMap
  res_refl h x := Ch.ρ_refl h x
  res_comp h₁ h₂ x := Ch.ρ_comp h₁ h₂ x

end CurveCharts

end Charts

section StageOne

open TensorProduct

variable {k : Type u} [Field k] {ι : Type u}

/-- **An `A`-point of the curve map on the charts**: maps `S s → O s ⊗ A` compatible with
restriction, reducing to `f0` over the residue field and to `f0` on the marked points. -/
structure CurvePoint (Ch : CurveCharts k ι) (A : ArtinLocalAlgebra k) where
  /-- The map on the chart `s`. -/
  pt : ∀ s, Ch.S s →ₐ[k] Ch.O s ⊗[k] A.carrier
  /-- `pt` commutes with restriction. -/
  pt_comm : ∀ {s t : Finset ι} (h : s ⊆ t) (x : Ch.S s),
    pt t (Ch.σ h x) = Algebra.TensorProduct.map (Ch.ρ h) (AlgHom.id k A.carrier) (pt s x)
  /-- `pt` reduces to `f0` over the residue field. -/
  pt_res : ∀ s (x : Ch.S s),
    Algebra.TensorProduct.map (AlgHom.id k (Ch.O s)) (toRes A) (pt s x) = Ch.f0 s x ⊗ₜ 1
  /-- `pt` is `f0` on the marked points. -/
  pt_fix : ∀ s (x : Ch.S s),
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ch.𝔟 s)) (AlgHom.id k A.carrier) (pt s x) =
      Ideal.Quotient.mk (Ch.𝔟 s) (Ch.f0 s x) ⊗ₜ 1

variable {Ch : CurveCharts k ι} {A : ArtinLocalAlgebra k} (E : SmallExtension A)

/-- Reduction to `A`. -/
abbrev piA (s : Finset ι) : Ch.O s ⊗[k] E.big.carrier →ₐ[k] Ch.O s ⊗[k] A.carrier :=
  Algebra.TensorProduct.map (AlgHom.id k _) E.π

/-- Restriction to the marked points. -/
abbrev piB (s : Finset ι) :
    Ch.O s ⊗[k] E.big.carrier →ₐ[k] (Ch.O s ⧸ Ch.𝔟 s) ⊗[k] E.big.carrier :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k _) (AlgHom.id k _)

/-- The constant map on the marked points. -/
abbrev fixB (s : Finset ι) : Ch.S s →ₐ[k] (Ch.O s ⧸ Ch.𝔟 s) ⊗[k] E.big.carrier :=
  (Algebra.TensorProduct.includeLeft : (Ch.O s ⧸ Ch.𝔟 s) →ₐ[k] _).comp
    ((Ideal.Quotient.mkₐ k _).comp (Ch.f0 s))

/-- Reduction to `A` is surjective. -/
theorem piA_surjective (s : Finset ι) : Function.Surjective (piA (Ch := Ch) E s) :=
  Algebra.TensorProduct.map_surjective _ _ (fun x => ⟨x, rfl⟩) E.surjective

/-- Restriction to the marked points is surjective. -/
theorem piB_surjective (s : Finset ι) : Function.Surjective (piB (Ch := Ch) E s) :=
  Algebra.TensorProduct.map_surjective _ _ Ideal.Quotient.mk_surjective (fun x => ⟨x, rfl⟩)

/-- The kernel of reduction to `A` is square-zero. -/
theorem ker_piA_mul (s : Finset ι) :
    RingHom.ker (piA (Ch := Ch) E s) * RingHom.ker (piA (Ch := Ch) E s) = ⊥ :=
  E.ker_tensor_mul_ker _

/-- The square-zero ideal `J ⊗ 𝔟` of the lifting problem across `C_A ∪ B_B`. -/
abbrev Ione (s : Finset ι) : Ideal (Ch.O s ⊗[k] E.big.carrier) :=
  RingHom.ker (piA (Ch := Ch) E s) ⊓ RingHom.ker (piB (Ch := Ch) E s)

/-- Two elements with the same reduction to `A` and the same restriction to the marked points
differ by an element of `Ione E s`. -/
theorem sub_mem_Ione {s : Finset ι} {x y : Ch.O s ⊗[k] E.big.carrier}
    (h1 : piA E s x = piA E s y) (h2 : piB E s x = piB E s y) : x - y ∈ Ione E s :=
  ⟨by simp [RingHom.mem_ker, h1], by simp [RingHom.mem_ker, h2]⟩

/-- The reduction of both restrictions to the marked points over `A`. -/
abbrev piAB (s : Finset ι) :
    Ch.O s ⊗[k] E.big.carrier →ₐ[k] (Ch.O s ⧸ Ch.𝔟 s) ⊗[k] A.carrier :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k _) E.π

/-- The kernel of `piAB` is the sum of the kernels of `piA` and `piB`. -/
theorem ker_piAB (s : Finset ι) :
    RingHom.ker (piAB (Ch := Ch) E s) = RingHom.ker (piA (Ch := Ch) E s) ⊔
      RingHom.ker (piB (Ch := Ch) E s) := by
  rw [Algebra.TensorProduct.map_ker _ _ Ideal.Quotient.mk_surjective E.surjective,
    Algebra.TensorProduct.lTensor_ker _ E.surjective,
    Algebra.TensorProduct.rTensor_ker _ Ideal.Quotient.mk_surjective, sup_comm]

/-- `piAB` factors through reduction to `A`. -/
theorem piAB_eq_left (s : Finset ι) (x : Ch.O s ⊗[k] E.big.carrier) :
    piAB E s x = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ch.𝔟 s)) (AlgHom.id k _)
      (piA E s x) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  rfl

/-- `piAB` factors through restriction to the marked points. -/
theorem piAB_eq_right (s : Finset ι) (x : Ch.O s ⊗[k] E.big.carrier) :
    piAB E s x = Algebra.TensorProduct.map (AlgHom.id k _) E.π (piB E s x) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  rfl

/-- **Common lifts exist**: a map `S_s → O_s ⊗ B` reducing to the given `A`-point and constant on
the marked points (smooth lifting across `C_A ∪ B_B`). -/
theorem exists_commonLift (p : CurvePoint Ch A) {s : Finset ι} (hs : s.Nonempty) :
    ∃ g : Ch.S s →ₐ[k] Ch.O s ⊗[k] E.big.carrier,
      (piA E s).comp g = p.pt s ∧ (piB E s).comp g = fixB E s := by
  haveI := Ch.smooth s hs
  let eA := Ideal.quotientKerAlgEquivOfSurjective (piA_surjective (Ch := Ch) E s)
  let eB := Ideal.quotientKerAlgEquivOfSurjective (piB_surjective (Ch := Ch) E s)
  have hA : ∀ x, eA.symm (piA E s x) = Ideal.Quotient.mk _ x := fun x =>
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply _ x
  have hB : ∀ x, eB.symm (piB E s x) = Ideal.Quotient.mk _ x := fun x =>
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply _ x
  obtain ⟨g, hg1, hg2⟩ := exists_lift_agreeing (RingHom.ker (piA (Ch := Ch) E s))
    (RingHom.ker (piB (Ch := Ch) E s)) (inf_mul_inf_eq_bot_of_mul_eq_bot (ker_piA_mul E s) _)
    (eA.symm.toAlgHom.comp (p.pt s)) (eB.symm.toAlgHom.comp (fixB E s)) (by
      intro a x y hx hy
      have hx' : piA E s x = p.pt s a := by
        apply eA.symm.injective
        rwa [hA]
      have hy' : piB E s y = fixB E s a := by
        apply eB.symm.injective
        rwa [hB]
      rw [← ker_piAB, RingHom.mem_ker, map_sub, piAB_eq_left, hx', piAB_eq_right, hy',
        p.pt_fix]
      simp)
  refine ⟨g, AlgHom.ext fun a => ?_, AlgHom.ext fun a => ?_⟩
  · apply eA.symm.injective
    rw [AlgHom.comp_apply, hA]
    exact congr($hg1 a)
  · apply eB.symm.injective
    rw [AlgHom.comp_apply, hB]
    exact congr($hg2 a)

end StageOne

section StageOneCover

open TensorProduct

variable {k : Type u} [Field k] {ι : Type u} {Ch : CurveCharts k ι} {A : ArtinLocalAlgebra k}
  (E : SmallExtension A)

/-- The restriction of `𝔟`-classes. -/
def ρbar {s t : Finset ι} (h : s ⊆ t) : (Ch.O s ⧸ Ch.𝔟 s) →ₐ[k] (Ch.O t ⧸ Ch.𝔟 t) :=
  Ideal.quotientMapₐ (Ch.𝔟 t) (Ch.ρ h) (fun x hx => Ch.ρ_mem h x hx)

/-- The restriction map of the thickened charts. -/
abbrev ψone {s t : Finset ι} (h : s ⊆ t) :
    Ch.O s ⊗[k] E.big.carrier →ₐ[k] Ch.O t ⊗[k] E.big.carrier :=
  Algebra.TensorProduct.map (Ch.ρ h) (AlgHom.id k _)

/-- Reduction to `A` commutes with restriction. -/
theorem piA_ψone {s t : Finset ι} (h : s ⊆ t) (x : Ch.O s ⊗[k] E.big.carrier) :
    piA E t (ψone E h x) =
      Algebra.TensorProduct.map (Ch.ρ h) (AlgHom.id k A.carrier) (piA E s x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restriction to the marked points commutes with restriction. -/
theorem piB_ψone {s t : Finset ι} (h : s ⊆ t) (x : Ch.O s ⊗[k] E.big.carrier) :
    piB E t (ψone E h x) =
      Algebra.TensorProduct.map (ρbar h) (AlgHom.id k _) (piB E s x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The chosen common lift. -/
def commonLift (p : CurvePoint Ch A) {s : Finset ι} (hs : s.Nonempty) :
    Ch.S s →ₐ[k] Ch.O s ⊗[k] E.big.carrier :=
  (exists_commonLift E p hs).choose

/-- The common lift reduces to the given `A`-point. -/
theorem piA_commonLift (p : CurvePoint Ch A) {s : Finset ι} (hs : s.Nonempty)
    (a : Ch.S s) : piA E s (commonLift E p hs a) = p.pt s a :=
  congr($((exists_commonLift E p hs).choose_spec.1) a)

/-- The common lift is constant on the marked points. -/
theorem piB_commonLift (p : CurvePoint Ch A) {s : Finset ι} (hs : s.Nonempty)
    (a : Ch.S s) : piB E s (commonLift E p hs a) = fixB E s a :=
  congr($((exists_commonLift E p hs).choose_spec.2) a)

/-- Restriction maps `Ione E s` into `Ione E t`. -/
theorem ψone_mem {s t : Finset ι} (h : s ⊆ t) (x : Ch.O s ⊗[k] E.big.carrier)
    (hx : x ∈ Ione E s) : ψone E h x ∈ Ione E t := by
  have h1 : piA E s x = 0 := RingHom.mem_ker.1 (Ideal.mem_inf.1 hx).1
  have h2 : piB E s x = 0 := RingHom.mem_ker.1 (Ideal.mem_inf.1 hx).2
  refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 ?_, RingHom.mem_ker.2 ?_⟩
  · rw [piA_ψone, h1, map_zero]
  · rw [piB_ψone, h2, map_zero]

/-- **The first-stage lifting problem** of an `A`-point `p` along a small extension `E`:
`P_s = O_s ⊗ B`, `I_s = J ⊗ 𝔟_s`, `φ_s` the class of a common lift. -/
def stageOne (p : CurvePoint Ch A) : NLiftCover Ch.toNChartData where
  P s := Ch.O s ⊗[k] E.big.carrier
  I s := Ione E s
  hI s := inf_mul_inf_eq_bot_of_mul_eq_bot (ker_piA_mul E s) _
  φ s hs := (Ideal.Quotient.mkₐ k _).comp (commonLift E p hs)
  ψ h := ψone E h
  ψ_refl h x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Ch.ρ_refl]
    | add x y hx hy => simp only [map_add, hx, hy]
  ψ_comp h₁ h₂ x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Ch.ρ_comp]
    | add x y hx hy => simp only [map_add, hx, hy]
  mem h x hx := ψone_mem E h x hx
  compat {s t} h hs a p' hp := by
    change Ideal.Quotient.mk (Ione E t) (ψone E h p') =
      Ideal.Quotient.mk (Ione E t) (commonLift E p (hs.mono h) (Ch.σ h a))
    have hp' : p' - commonLift E p hs a ∈ Ione E s := Ideal.Quotient.eq.1 hp
    rw [Ideal.Quotient.eq]
    have e1 := ψone_mem E h _ hp'
    rw [map_sub] at e1
    have e2 : ψone E h (commonLift E p hs a) - commonLift E p (hs.mono h) (Ch.σ h a) ∈
        Ione E t := by
      refine sub_mem_Ione E ?_ ?_
      · rw [piA_ψone, piA_commonLift, piA_commonLift, p.pt_comm]
      · rw [piB_ψone, piB_commonLift, piB_commonLift]
        simp only [fixB, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk, Ch.f0_comm]
        rfl
    have := (Ione E t).add_mem e1 e2
    convert this using 1
    ring

variable {E} {E' : SmallExtension A}

/-- Reduction to `A` commutes with a quotient map of small extensions. -/
theorem piA_mapq (q : E.QuotientMap E') {s : Finset ι}
    (y : Ch.O s ⊗[k] E.big.carrier) :
    piA E' s (Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom y) = piA E s y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [← AlgHom.comp_apply E'.π, q.comp_π]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restriction to the marked points commutes with a quotient map of small extensions. -/
theorem piB_mapq (q : E.QuotientMap E') {s : Finset ι}
    (y : Ch.O s ⊗[k] E.big.carrier) :
    piB E' s (Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom y) =
      Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom (piB E s y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A quotient map of small extensions maps `Ione E s` into `Ione E' s`. -/
theorem mapq_mem (q : E.QuotientMap E') {s : Finset ι} (x : Ch.O s ⊗[k] E.big.carrier)
    (hx : x ∈ Ione E s) :
    Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom x ∈ Ione E' s := by
  have h1 : piA E s x = 0 := RingHom.mem_ker.1 (Ideal.mem_inf.1 hx).1
  have h2 : piB E s x = 0 := RingHom.mem_ker.1 (Ideal.mem_inf.1 hx).2
  refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 ?_, RingHom.mem_ker.2 ?_⟩
  · rw [piA_mapq, h1]
  · rw [piB_mapq, h2, map_zero]

/-- The quotient of the first-stage lifting problem along a quotient map of small extensions. -/
def stageOneMap (q : E.QuotientMap E') (p : CurvePoint Ch A) :
    (stageOne E p).Hom (stageOne E' p) where
  sq s := Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom
  mem s x hx := mapq_mem q x hx
  compat s hs a p₀ hp := by
    obtain ⟨p', rfl⟩ : ∃ p' : Ch.O s ⊗[k] E.big.carrier, p' = p₀ := ⟨p₀, rfl⟩
    change Ideal.Quotient.mk (Ione E' s) (Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom p') =
      Ideal.Quotient.mk (Ione E' s) (commonLift E' p hs a)
    rw [Ideal.Quotient.eq]
    have hp' : p' - commonLift E p hs a ∈ Ione E s := Ideal.Quotient.eq.1 hp
    have e1 := mapq_mem q _ hp'
    have e2 : Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom (commonLift E p hs a) -
        commonLift E' p hs a ∈ Ione E' s := by
      refine sub_mem_Ione E' ?_ ?_
      · rw [piA_mapq, piA_commonLift, piA_commonLift]
      · rw [piB_mapq, piB_commonLift, piB_commonLift]
        simp
    rw [map_sub] at e1
    have := (Ione E' s).add_mem e1 e2
    convert this using 1
    ring
  comm h x := by
    change Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom (ψone E h x) =
      ψone E' h (Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]

end StageOneCover

namespace Cech

section TensorPresheaf

open scoped TensorProduct

variable {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι] (F : CechPresheaf.{u} k ι)
  (J : Type u) [AddCommGroup J] [Module k J]

/-- The presheaf `s ↦ J ⊗_k F(s)` on the nerve. -/
def tensorLeft : CechPresheaf.{u} k ι where
  obj s := J ⊗[k] F.obj s
  addCommGroup _ := inferInstance
  module _ := inferInstance
  res h := LinearMap.lTensor J (F.res h)
  res_refl h x := by
    have : F.res h = LinearMap.id := LinearMap.ext (F.res_refl h)
    simp [this]
  res_comp h₁ h₂ x := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    congr 2
    exact LinearMap.ext (F.res_comp h₁ h₂)

/-- Čech `2`-cochains: sections over the triple intersections. -/
abbrev C2 : Type _ := ∀ i j l : ι, F.obj {i, j, l}

/-- The Čech differential `C¹ → C²`. -/
def d1 : F.C1 →ₗ[k] (C2 F) where
  toFun b i j l := F.res (CechPresheaf.pair_sub_triple₂₃ i j l) (b j l) -
    F.res (CechPresheaf.pair_sub_triple₁₃ i j l) (b i l)
    + F.res (CechPresheaf.pair_sub_triple₁₂ i j l) (b i j)
  map_add' b b' := by
    funext i j l
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' c b := by funext i j l; simp [smul_sub, smul_add]

/-- The Čech `1`-cocycles are the kernel of `d1`. -/
theorem Z1_eq_ker_d1 : F.Z1 = LinearMap.ker (d1 F) := by
  ext b
  simp only [LinearMap.mem_ker, d1, LinearMap.coe_mk, AddHom.coe_mk]
  exact ⟨fun h => funext fun i => funext fun j => funext (h i j),
    fun h i j l => congrFun (congrFun (congrFun h i) j) l⟩

section Comparison

variable [Fintype ι]

/-- `J ⊗ C⁰(F) ≃ C⁰(J ⊗ F)` (finite products commute with tensor products). -/
def chi0 : J ⊗[k] F.C0 ≃ₗ[k] ((tensorLeft F) J).C0 :=
  TensorProduct.piRight k k J (fun i => F.obj {i})

/-- `J ⊗ C¹(F) ≃ C¹(J ⊗ F)`. -/
def chi1 : J ⊗[k] F.C1 ≃ₗ[k] ((tensorLeft F) J).C1 :=
  (TensorProduct.piRight k k J (fun i => ∀ j, F.obj {i, j})).trans
    (LinearEquiv.piCongrRight fun i => TensorProduct.piRight k k J (fun j => F.obj {i, j}))

/-- `J ⊗ C²(F) ≃ C²(J ⊗ F)`. -/
def chi2 : J ⊗[k] (C2 F) ≃ₗ[k] (C2 ((tensorLeft F) J)) :=
  (TensorProduct.piRight k k J (fun i => ∀ j l, F.obj {i, j, l})).trans
    (LinearEquiv.piCongrRight fun i =>
      (TensorProduct.piRight k k J (fun j => ∀ l, F.obj {i, j, l})).trans
        (LinearEquiv.piCongrRight fun j =>
          TensorProduct.piRight k k J (fun l => F.obj {i, j, l})))

/-- `chi0` on pure tensors: `j ⊗ c ↦ (i ↦ j ⊗ c i)`. -/
theorem chi0_tmul (j : J) (c : F.C0) (i : ι) : (chi0 F) J (j ⊗ₜ c) i = j ⊗ₜ c i :=
  congrFun (TensorProduct.piRightHom_tmul k k J (fun i => F.obj {i}) j c) i

/-- `chi1` on pure tensors: `j ⊗ b ↦ (i i' ↦ j ⊗ b i i')`. -/
theorem chi1_tmul (j : J) (b : F.C1) (i i' : ι) :
    (chi1 F) J (j ⊗ₜ b) i i' = j ⊗ₜ b i i' :=
  congrFun (TensorProduct.piRightHom_tmul k k J (fun i' => F.obj {i, i'}) j (b i)) i'

/-- `chi2` on pure tensors: `j ⊗ b ↦ (i i' i'' ↦ j ⊗ b i i' i'')`. -/
theorem chi2_tmul (j : J) (b : (C2 F)) (i i' i'' : ι) :
    (chi2 F) J (j ⊗ₜ b) i i' i'' = j ⊗ₜ b i i' i'' :=
  congrFun (TensorProduct.piRightHom_tmul k k J (fun i'' => F.obj {i, i', i''}) j (b i i')) i''

/-- `chi0` and `chi1` intertwine `J ⊗ d0` with the differential `d0` of `J ⊗ F`. -/
theorem chi1_lTensor_d0 (w : J ⊗[k] F.C0) :
    (chi1 F) J (LinearMap.lTensor J F.d0 w) = ((tensorLeft F) J).d0 ((chi0 F) J w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul j c =>
    funext i i'
    rw [LinearMap.lTensor_tmul, chi1_tmul]
    change _ = (tensorLeft F J).res _ ((chi0 F) J (j ⊗ₜ c) i') - (tensorLeft F J).res _
      ((chi0 F) J (j ⊗ₜ c) i)
    rw [chi0_tmul, chi0_tmul]
    change _ = LinearMap.lTensor J (F.res _) _ - LinearMap.lTensor J (F.res _) _
    simp only [LinearMap.lTensor_tmul, CechPresheaf.d0, LinearMap.coe_mk, AddHom.coe_mk,
      TensorProduct.tmul_sub]
    rfl

/-- The restriction maps of `J ⊗ F` are `J ⊗ F.res`. -/
theorem tensorLeft_res {s t : Finset ι} (h : s ⊆ t) (x : J ⊗[k] F.obj s) :
    ((tensorLeft F) J).res h x = LinearMap.lTensor J (F.res h) x := rfl

/-- `chi1` and `chi2` intertwine `J ⊗ d1` with the differential `d1` of `J ⊗ F`. -/
theorem chi2_lTensor_d1 (w : J ⊗[k] F.C1) :
    (chi2 F) J (LinearMap.lTensor J (d1 F) w) = (d1 ((tensorLeft F) J)) ((chi1 F) J w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul j b =>
    funext i i' i''
    rw [LinearMap.lTensor_tmul, chi2_tmul]
    simp only [Cech.d1, LinearMap.coe_mk, AddHom.coe_mk, tensorLeft_res, chi1_tmul,
      LinearMap.lTensor_tmul, TensorProduct.tmul_sub, TensorProduct.tmul_add]
    rfl

/-- The coboundary map `C⁰ → Z¹`. -/
def d0Z : F.C0 →ₗ[k] F.Z1 := F.d0.codRestrict F.Z1 F.isCocycle_d0

/-- The Čech `1`-coboundaries are the range of `d0Z`. -/
theorem B1_eq_range : F.B1 = LinearMap.range (d0Z F) := by
  ext x
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

/-- `J ⊗ Z¹(F) → Z¹(J ⊗ F)`. -/
def zeta : J ⊗[k] F.Z1 →ₗ[k] ((tensorLeft F) J).Z1 :=
  (((chi1 F) J).toLinearMap ∘ₗ LinearMap.lTensor J F.Z1.subtype).codRestrict ((tensorLeft F) J).Z1
    (fun w => by
      rw [Z1_eq_ker_d1, LinearMap.mem_ker]
      change (d1 ((tensorLeft F) J)) ((chi1 F) J (LinearMap.lTensor J F.Z1.subtype w)) = 0
      rw [← chi2_lTensor_d1, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      have : (d1 F) ∘ₗ F.Z1.subtype = 0 :=
        LinearMap.ext fun x => LinearMap.mem_ker.1 ((Z1_eq_ker_d1 (F := F)).le x.2)
      rw [this]
      simp)

/-- `zeta` is `chi1` applied to the inclusion `J ⊗ Z¹(F) → J ⊗ C¹(F)`. -/
theorem zeta_apply (w : J ⊗[k] F.Z1) :
    (((zeta F) J w : ((tensorLeft F) J).Z1) : ((tensorLeft F) J).C1) =
      (chi1 F) J (LinearMap.lTensor J F.Z1.subtype w) := rfl

/-- `zeta` maps `J ⊗ d0Z` to the differential `d0` of `J ⊗ F`. -/
theorem zeta_lTensor_d0Z (y : J ⊗[k] F.C0) :
    (((zeta F) J (LinearMap.lTensor J (d0Z F) y) : ((tensorLeft F) J).Z1) : ((tensorLeft F) J).C1) =
      ((tensorLeft F) J).d0 ((chi0 F) J y) := by
  rw [zeta_apply, ← chi1_lTensor_d0, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  rfl

/-- `d1` vanishes on cocycles. -/
theorem d1_eq_zero_of_mem_Z1 {b : F.C1} (hb : b ∈ F.Z1) : (d1 F) b = 0 := by
  rwa [Z1_eq_ker_d1] at hb

/-- The sequence `Z¹(F) → C¹(F) → C²(F)` is exact. -/
theorem exact_subtype_d1 : Function.Exact F.Z1.subtype (d1 F) := by
  rw [LinearMap.exact_iff, Submodule.range_subtype, Z1_eq_ker_d1]

variable [Module.Flat k J]

/-- `zeta` is injective for flat `J`. -/
theorem zeta_injective : Function.Injective ((zeta F) J) := by
  intro x y hxy
  have h1 : (chi1 F) J (LinearMap.lTensor J F.Z1.subtype x) =
      (chi1 F) J (LinearMap.lTensor J F.Z1.subtype y) := by
    simpa only [zeta_apply] using congrArg Subtype.val hxy
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := J) F.Z1.subtype
    F.Z1.subtype_injective (((chi1 F) J).injective h1)

/-- `zeta` is surjective for flat `J`. -/
theorem zeta_surjective : Function.Surjective ((zeta F) J) := by
  intro z
  have h0 : (d1 ((tensorLeft F) J)) z.1 = 0 := d1_eq_zero_of_mem_Z1 _ z.2
  have h1 : LinearMap.lTensor J (d1 F) (((chi1 F) J).symm z.1) = 0 := by
    apply ((chi2 F) J).injective
    rw [chi2_lTensor_d1, LinearEquiv.apply_symm_apply, h0, map_zero]
  obtain ⟨v, hv⟩ := (Module.Flat.lTensor_exact J (exact_subtype_d1 F)) _ |>.1 h1
  refine ⟨v, Subtype.ext ?_⟩
  rw [zeta_apply, hv, LinearEquiv.apply_symm_apply]

/-- `zeta x` is a coboundary of `J ⊗ F` if and only if `x` lies in the image of `J ⊗ d0Z`. -/
theorem zeta_mem_B1_iff (x : J ⊗[k] F.Z1) :
    (zeta F) J x ∈ ((tensorLeft F) J).B1 ↔ x ∈ LinearMap.range (LinearMap.lTensor J (d0Z F)) := by
  constructor
  · rintro ⟨c', hc'⟩
    refine ⟨((chi0 F) J).symm c', (zeta_injective F) J (Subtype.ext ?_)⟩
    rw [zeta_lTensor_d0Z, LinearEquiv.apply_symm_apply]
    exact hc'
  · rintro ⟨y, rfl⟩
    exact ⟨(chi0 F) J y, (zeta_lTensor_d0Z F J y).symm⟩

/-- The sequence `C⁰(F) → Z¹(F) → H¹(F)` is exact. -/
theorem exact_d0Z_mkQ : Function.Exact (d0Z F) F.B1.mkQ := by
  rw [LinearMap.exact_iff, Submodule.ker_mkQ, B1_eq_range]

/-- The sequence `J ⊗ C⁰(F) → J ⊗ Z¹(F) → J ⊗ H¹(F)` is exact. -/
theorem exact_lTensor_d0Z :
    Function.Exact (LinearMap.lTensor J (d0Z F)) (LinearMap.lTensor J F.B1.mkQ) :=
  lTensor_exact J (exact_d0Z_mkQ F) F.B1.mkQ_surjective

/-- The comparison `J ⊗ H¹(F) → H¹(J ⊗ F)`. -/
def tensorH1Hom : J ⊗[k] F.H1 →ₗ[k] ((tensorLeft F) J).H1 :=
  (Submodule.liftQ (LinearMap.ker (LinearMap.lTensor J F.B1.mkQ))
    (((tensorLeft F) J).B1.mkQ ∘ₗ (zeta F) J) (by
      intro x hx
      rw [((exact_lTensor_d0Z F) J).linearMap_ker_eq] at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 (((zeta_mem_B1_iff F) J x).2 hx))) ∘ₗ
    ((LinearMap.lTensor J F.B1.mkQ).quotKerEquivOfSurjective
      (LinearMap.lTensor_surjective J F.B1.mkQ_surjective)).symm.toLinearMap

/-- `tensorH1Hom` sends the class of `x ∈ J ⊗ Z¹(F)` to the class of `zeta x`. -/
theorem tensorH1Hom_lTensor_mkQ (x : J ⊗[k] F.Z1) :
    (tensorH1Hom F) J (LinearMap.lTensor J F.B1.mkQ x) =
      ((tensorLeft F) J).B1.mkQ ((zeta F) J x) := by
  have : ((LinearMap.lTensor J F.B1.mkQ).quotKerEquivOfSurjective
      (LinearMap.lTensor_surjective J F.B1.mkQ_surjective)).symm
        (LinearMap.lTensor J F.B1.mkQ x) =
      Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [tensorH1Hom, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
  rfl

/-- `tensorH1Hom` is bijective for flat `J`. -/
theorem tensorH1Hom_bijective : Function.Bijective ((tensorH1Hom F) J) := by
  constructor
  · intro t t' htt
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective J F.B1.mkQ_surjective t
    obtain ⟨x', rfl⟩ := LinearMap.lTensor_surjective J F.B1.mkQ_surjective t'
    rw [tensorH1Hom_lTensor_mkQ, tensorH1Hom_lTensor_mkQ] at htt
    have h := (Submodule.Quotient.eq _).1 htt
    rw [← map_sub, (zeta_mem_B1_iff F) J] at h
    have h0 := (((exact_lTensor_d0Z F) J) (x - x')).2 (LinearMap.mem_range.1 h)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  · intro q
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨x, rfl⟩ := (zeta_surjective F) J z
    exact ⟨_, (tensorH1Hom_lTensor_mkQ F) J x⟩

/-- **`H¹(J ⊗ F) ≅ J ⊗ H¹(F)`** for a flat `k`-module `J` (e.g. a finite-dimensional vector space
over a field `k`) and a presheaf on the nerve of a finite cover: Čech `H¹` commutes with the
exact functor `J ⊗ -`. -/
def tensorH1Equiv : J ⊗[k] F.H1 ≃ₗ[k] ((tensorLeft F) J).H1 :=
  LinearEquiv.ofBijective ((tensorH1Hom F) J) ((tensorH1Hom_bijective F) J)

/-- On classes, `tensorH1Equiv` is `j ⊗ [z] ↦ [j ⊗ z]`; this characterises it (and gives its
naturality in `J`). -/
theorem tensorH1Equiv_tmul (j : J) (z : F.Z1)
    (h : ((tensorLeft F) J).IsCocycle (fun i i' => j ⊗ₜ[k] z.1 i i')) :
    (tensorH1Equiv F) J (j ⊗ₜ[k] F.B1.mkQ z) =
      ((tensorLeft F) J).cls (fun i i' => j ⊗ₜ[k] z.1 i i') h := by
  change (tensorH1Hom F) J (LinearMap.lTensor J F.B1.mkQ (j ⊗ₜ[k] z)) = _
  rw [tensorH1Hom_lTensor_mkQ]
  refine congrArg (Submodule.Quotient.mk (p := ((tensorLeft F) J).B1)) (Subtype.ext ?_)
  funext i i'
  exact chi1_tmul F J j z.1 i i'

end Comparison

end TensorPresheaf

section DerivationTensor

open scoped TensorProduct

variable {k S N : Type*} [CommRing k] [CommRing S] [Algebra k S] [AddCommGroup N] [Module k N]
  [Module S N] [IsScalarTower k S N] (J : Type*) [AddCommGroup J] [Module k J]

/-- `n ↦ n ⊗ j`, as an `S`-linear map `N → N ⊗_k J`. -/
def tmulRight (j : J) : N →ₗ[S] N ⊗[k] J :=
  (TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N)
    (LinearMap.toSpanSingleton k J j)) ∘ₗ
      (TensorProduct.AlgebraTensorModule.rid k S N).symm.toLinearMap

/-- `tmulRight J j n = n ⊗ j`. -/
theorem tmulRight_apply (j : J) (n : N) : tmulRight (S := S) J j n = n ⊗ₜ[k] j := by
  simp [tmulRight]

/-- The comparison `Der_k(S, N) ⊗_k J → Der_k(S, N ⊗_k J)`, `D ⊗ j ↦ (s ↦ D s ⊗ j)`. -/
def derivationTensorHom : Derivation k S N ⊗[k] J →ₗ[k] Derivation k S (N ⊗[k] J) :=
  TensorProduct.lift (LinearMap.mk₂ k (fun D j => (tmulRight (S := S) J j).compDer D)
    (fun D D' j => by ext s; simp [tmulRight_apply, TensorProduct.add_tmul])
    (fun c D j => by ext s; simp [tmulRight_apply, TensorProduct.smul_tmul'])
    (fun D j j' => by ext s; simp [tmulRight_apply, TensorProduct.tmul_add])
    (fun c D j => by ext s; simp [tmulRight_apply, TensorProduct.tmul_smul]))

/-- `derivationTensorHom` on pure tensors: `(D ⊗ j) s = D s ⊗ j`. -/
theorem derivationTensorHom_tmul (D : Derivation k S N) (j : J) (s : S) :
    derivationTensorHom J (D ⊗ₜ[k] j) s = D s ⊗ₜ[k] j := by
  simp [derivationTensorHom, tmulRight_apply]

section Basis

variable {κ : Type*} [Fintype κ] (b : Module.Basis κ k J)

/-- The `i`-th coordinate `N ⊗_k J → N` with respect to a basis of `J`, `S`-linear. -/
def projBasis (i : κ) : N ⊗[k] J →ₗ[S] N :=
  (TensorProduct.AlgebraTensorModule.rid k S N).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N) (b.coord i)

/-- `projBasis J b i (n ⊗ j) = b.coord i j • n`. -/
theorem projBasis_apply (i : κ) (n : N) (j : J) :
    projBasis (S := S) J b i (n ⊗ₜ[k] j) = b.coord i j • n := by
  simp [projBasis]

/-- Every `x ∈ N ⊗ J` is `∑ i, projBasis J b i x ⊗ b i`. -/
theorem sum_projBasis_tmul (x : N ⊗[k] J) :
    ∑ i, projBasis (S := S) J b i x ⊗ₜ[k] b i = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]
  | tmul n j =>
    simp only [projBasis_apply, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
    congr 1
    simpa using b.sum_repr j

/-- The inverse of `derivationTensorHom` for a finite basis of `J`. -/
def derivationTensorInv : Derivation k S (N ⊗[k] J) →ₗ[k] Derivation k S N ⊗[k] J where
  toFun D := ∑ i, ((projBasis (S := S) J b i).compDer D) ⊗ₜ[k] b i
  map_add' D D' := by
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c D := by
    simp only [RingHom.id_apply, Finset.smul_sum, TensorProduct.smul_tmul']
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ext s
    simp

/-- `derivationTensorInv` is a right inverse of `derivationTensorHom`. -/
theorem derivationTensorHom_inv (D : Derivation k S (N ⊗[k] J)) :
    derivationTensorHom J (derivationTensorInv J b D) = D := by
  refine Derivation.ext fun s => ?_
  change (derivationTensorHom J (∑ i, ((projBasis (S := S) J b i).compDer D) ⊗ₜ[k] b i)) s = D s
  rw [map_sum, ← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp only [Derivation.coeFnAddMonoidHom_apply, derivationTensorHom_tmul]
  exact sum_projBasis_tmul J b (D s)

/-- `derivationTensorInv` is a left inverse of `derivationTensorHom`. -/
theorem derivationTensorInv_hom (t : Derivation k S N ⊗[k] J) :
    derivationTensorInv J b (derivationTensorHom J t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul D j =>
    change ∑ i, ((projBasis (S := S) J b i).compDer (derivationTensorHom J (D ⊗ₜ[k] j))) ⊗ₜ[k]
      b i = _
    have : ∀ i, (projBasis (S := S) J b i).compDer (derivationTensorHom J (D ⊗ₜ[k] j)) =
        b.coord i j • D := fun i => by
      refine Derivation.ext fun s => ?_
      change projBasis (S := S) J b i (derivationTensorHom J (D ⊗ₜ[k] j) s) = _
      rw [derivationTensorHom_tmul, projBasis_apply]
      rfl
    simp only [this, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
    congr 1
    simpa using b.sum_repr j

/-- **`Der_k(S, N ⊗_k J) ≅ Der_k(S, N) ⊗_k J`** for a `k`-module `J` with a finite basis
(e.g. a finite-dimensional vector space over a field `k`); on pure tensors `D ⊗ j ↦ (s ↦ D s ⊗ j)`
(`derivationTensorHom_tmul`), whence its naturality in `J`. -/
def derivationTensorEquiv : Derivation k S N ⊗[k] J ≃ₗ[k] Derivation k S (N ⊗[k] J) :=
  LinearEquiv.ofLinear (derivationTensorHom J) (derivationTensorInv J b)
    (LinearMap.ext (derivationTensorHom_inv J b)) (LinearMap.ext (derivationTensorInv_hom J b))

/-- `derivationTensorEquiv` on pure tensors: `(D ⊗ j) s = D s ⊗ j`. -/
theorem derivationTensorEquiv_tmul (D : Derivation k S N) (j : J) (s : S) :
    derivationTensorEquiv J b (D ⊗ₜ[k] j) s = D s ⊗ₜ[k] j :=
  derivationTensorHom_tmul J D j s

end Basis

end DerivationTensor

section SquareZeroDerivations

variable {k S P : Type*} [CommRing k] [CommRing S] [CommRing P] [Algebra k S] [Algebra k P]
  (I : Ideal P)

variable {I}

variable {M : Type*} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
  {φ : S →ₐ[k] P ⧸ I} (e : I ≃ₗ[k] M)

/-- The compatibility of an identification `e : I ≃ M` with the action of `S` on `M`:
multiplication in `P` by a lift of `φ s` is `s •`. -/
def IsEquivariantFor (φ : S →ₐ[k] P ⧸ I) (e : I ≃ₗ[k] M) [Module S M] : Prop :=
  ∀ (s : S) (p : P), Ideal.Quotient.mk I p = φ s →
    ∀ x : I, e ⟨p * x, I.mul_mem_left p x.2⟩ = s • e x

/-- **Derivations along `φ` with values in a square-zero ideal are `k`-derivations into the
`S`-module `M`**, for any equivariant identification `e : I ≃ M`. -/
def derivEquivDerivation (he : IsEquivariantFor φ e) :
    Deriv I φ ≃ₗ[k] Derivation k S M where
  toFun D :=
    { toLinearMap := e.toLinearMap ∘ₗ D.1
      map_one_eq_zero' := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, D.map_one, map_zero]
      leibniz' := fun a b => by
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (φ a)
        obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (φ b)
        have h := D.leibniz a b p q hp hq
        have h' : D.1 (a * b) = ⟨p * (D.1 b : P), I.mul_mem_left p (D.1 b).2⟩ +
            ⟨q * (D.1 a : P), I.mul_mem_left q (D.1 a).2⟩ := Subtype.ext h
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h', map_add, smul_eq_mul]
        rw [he a p hp, he b q hq] }
  map_add' D D' := by ext s; simp
  map_smul' c D := by ext s; simp
  invFun D' := ⟨e.symm.toLinearMap ∘ₗ D'.toLinearMap, fun a b p q hp hq => by
    have key : ∀ (s : S) (p : P), Ideal.Quotient.mk I p = φ s → ∀ y : M,
        ((e.symm (s • y) : I) : P) = p * (e.symm y : P) := fun s p hp y => by
      have h := he s p hp (e.symm y)
      rw [e.apply_symm_apply] at h
      have h2 := congrArg e.symm h
      rw [e.symm_apply_apply] at h2
      exact (congrArg Subtype.val h2).symm
    change ((e.symm (D' (a * b)) : I) : P) = _
    rw [D'.leibniz, map_add, Submodule.coe_add, key a p hp, key b q hq]
    rfl⟩
  left_inv D := Subtype.ext (LinearMap.ext fun s => by simp)
  right_inv D := Derivation.ext fun s => by
    show e (e.symm (D s)) = D s
    simp

end SquareZeroDerivations

section PresheafIso

open scoped TensorProduct

variable {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι]

/-- An isomorphism of presheaves of `k`-modules on the nerve of a cover. -/
structure Iso (F G : CechPresheaf.{u} k ι) where
  /-- The component at `s`. -/
  equiv : ∀ s : Finset ι, F.obj s ≃ₗ[k] G.obj s
  /-- The components commute with restriction. -/
  map_res : ∀ {s t : Finset ι} (h : s ⊆ t) (x : F.obj s),
    equiv t (F.res h x) = G.res h (equiv s x)

namespace Iso

variable {F G : CechPresheaf.{u} k ι} (e : Iso F G)

/-- The underlying morphism. -/
def hom : CechPresheaf.Hom F G := ⟨fun s => (e.equiv s).toLinearMap, e.map_res⟩

/-- The inverse isomorphism. -/
def symm : Iso G F where
  equiv s := (e.equiv s).symm
  map_res {s t} h x := by
    apply (e.equiv t).injective
    rw [e.map_res, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The induced isomorphism on first Čech cohomology. -/
def h1Equiv : F.H1 ≃ₗ[k] G.H1 :=
  LinearEquiv.ofLinear e.hom.h1 e.symm.hom.h1
    (LinearMap.ext fun z => by
      obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.mkQ_surjective _ z
      have hb' : G.IsCocycle b := hb
      change e.hom.h1 (e.symm.hom.h1 (G.cls b hb')) = G.cls b hb'
      rw [CechPresheaf.Hom.h1_cls, CechPresheaf.Hom.h1_cls]
      refine congrArg (Submodule.Quotient.mk (p := G.B1)) (Subtype.ext ?_)
      funext i j
      exact (e.equiv _).apply_symm_apply _)
    (LinearMap.ext fun z => by
      obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.mkQ_surjective _ z
      have hb' : F.IsCocycle b := hb
      change e.symm.hom.h1 (e.hom.h1 (F.cls b hb')) = F.cls b hb'
      rw [CechPresheaf.Hom.h1_cls, CechPresheaf.Hom.h1_cls]
      refine congrArg (Submodule.Quotient.mk (p := F.B1)) (Subtype.ext ?_)
      funext i j
      exact (e.equiv _).symm_apply_apply _)

/-- `h1Equiv` sends the class of a cocycle `b` to the class of its image. -/
theorem h1Equiv_cls {b : F.C1} (hb : F.IsCocycle b) :
    e.h1Equiv (F.cls b hb) = G.cls (e.hom.c1 b) (e.hom.isCocycle_c1 hb) := rfl

/-- Naturality of `h1Equiv` for compatible morphisms. -/
theorem h1Equiv_natural {F' G' : CechPresheaf.{u} k ι} (e' : Iso F' G')
    (m : CechPresheaf.Hom F F') (n : CechPresheaf.Hom G G')
    (h : ∀ (s : Finset ι) (x : F.obj s), e'.equiv s (m.map s x) = n.map s (e.equiv s x))
    (z : F.H1) : e'.h1Equiv (m.h1 z) = n.h1 (e.h1Equiv z) := by
  obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.mkQ_surjective _ z
  have hb' : F.IsCocycle b := hb
  change e'.hom.h1 (m.h1 (F.cls b hb')) = n.h1 (e.hom.h1 (F.cls b hb'))
  rw [CechPresheaf.Hom.h1_cls, CechPresheaf.Hom.h1_cls, CechPresheaf.Hom.h1_cls,
    CechPresheaf.Hom.h1_cls]
  refine congrArg (Submodule.Quotient.mk (p := G'.B1)) (Subtype.ext ?_)
  funext i j
  exact h _ _

end Iso

/-- `q ⊗ id` and `id ⊗ g` commute. -/
theorem rTensor_lTensor_comm {A B C D : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [AddCommMonoid C] [AddCommMonoid D] [Module k A] [Module k B] [Module k C] [Module k D] (q : A →ₗ[k] B)
    (g : C →ₗ[k] D) (x : A ⊗[k] C) :
    LinearMap.rTensor D q (LinearMap.lTensor A g x) =
      LinearMap.lTensor B g (LinearMap.rTensor C q x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (F : CechPresheaf.{u} k ι) {J J' : Type u} [AddCommGroup J] [Module k J]
  [AddCommGroup J'] [Module k J']

/-- Change of the tensor factor: the morphism `J ⊗ F → J' ⊗ F`, `q ⊗ id`. -/
def tensorMap (q : J →ₗ[k] J') : ((tensorLeft F) J).Hom ((tensorLeft F) J') where
  map s := LinearMap.rTensor (F.obj s) q
  map_res {s t} h x := by
    change LinearMap.rTensor (F.obj t) q (LinearMap.lTensor J (F.res h) x) =
      LinearMap.lTensor J' (F.res h) (LinearMap.rTensor (F.obj s) q x)
    exact rTensor_lTensor_comm q (F.res h) x

/-- For a cocycle `z` of `F`, `j ⊗ z` is a cocycle of `J ⊗ F`. -/
theorem tmul_isCocycle (j : J) (z : F.Z1) :
    ((tensorLeft F) J).IsCocycle (fun i i' => j ⊗ₜ[k] z.1 i i') := by
  intro i i' i''
  have h : j ⊗ₜ[k] (F.res (CechPresheaf.pair_sub_triple₂₃ i i' i'') (z.1 i' i'')) -
      j ⊗ₜ[k] (F.res (CechPresheaf.pair_sub_triple₁₃ i i' i'') (z.1 i i'')) +
      j ⊗ₜ[k] (F.res (CechPresheaf.pair_sub_triple₁₂ i i' i'') (z.1 i i')) = 0 := by
    rw [← TensorProduct.tmul_sub, ← TensorProduct.tmul_add]
    have := z.2 i i' i''
    rw [this, TensorProduct.tmul_zero]
  exact h

variable [Fintype ι] [Module.Flat k J] [Module.Flat k J']

/-- **Naturality of `tensorH1Equiv` in `J`.** -/
theorem tensorMap_h1_tensorH1Equiv (q : J →ₗ[k] J') (x : J ⊗[k] F.H1) :
    ((tensorMap F) q).h1 ((tensorH1Equiv F) J x) =
      (tensorH1Equiv F) J' (LinearMap.rTensor F.H1 q x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul j z =>
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    rw [Cech.tensorH1Equiv_tmul F J j z ((tmul_isCocycle F) j z)]
    simp only [LinearMap.rTensor_tmul]
    rw [Cech.tensorH1Equiv_tmul F J' (q j) z ((tmul_isCocycle F) (q j) z)]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end PresheafIso

end Cech

section ThetaOne

open TensorProduct

variable {k : Type u} [Field k] {ι : Type u} {Ch : CurveCharts k ι} {A : ArtinLocalAlgebra k}
  (E : SmallExtension A)

/-- The inclusion of `𝔟 s`, `k`-linearly. -/
def ιB (s : Finset ι) : Ch.𝔟 s →ₗ[k] Ch.O s where
  toFun n := n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The sequence `𝔟 s → O s → O s / 𝔟 s` is exact. -/
theorem exact_ιB (s : Finset ι) :
    Function.Exact (ιB (Ch := Ch) s) (Ideal.Quotient.mkₐ k (Ch.𝔟 s)).toLinearMap := by
  intro y
  simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    Set.mem_range]
  exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨n, hn⟩ => hn ▸ n.2⟩

/-- The sequence `J → B → A` of a small extension is exact. -/
theorem exact_kernel : Function.Exact E.kernel.subtype E.π.toLinearMap := by
  intro y
  exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨n, hn⟩ => hn ▸ n.2⟩

/-- `𝔟_s ⊗ J → O_s ⊗ B`. -/
abbrev mapBJ (s : Finset ι) : Ch.𝔟 s ⊗[k] E.kernel →ₗ[k] Ch.O s ⊗[k] E.big.carrier :=
  TensorProduct.map (ιB s) E.kernel.subtype

/-- `𝔟_s ⊗ J → O_s ⊗ B` is injective. -/
theorem mapBJ_injective (s : Finset ι) : Function.Injective (mapBJ (Ch := Ch) E s) :=
  TensorProduct.map_injective_of_flat_flat _ _ (fun _ _ h => Subtype.ext h)
    E.kernel.subtype_injective

/-- `Ione E s` is the image of `𝔟_s ⊗ J` in `O_s ⊗ B`. -/
theorem mem_Ione_iff (s : Finset ι) (x : Ch.O s ⊗[k] E.big.carrier) :
    x ∈ Ione E s ↔ x ∈ LinearMap.range (mapBJ (Ch := Ch) E s) := by
  rw [mem_range_map_iff (exact_ιB s) Ideal.Quotient.mk_surjective (exact_kernel E) E.surjective
    E.kernel.subtype_injective, ← algMap_id_apply, ← algMap_left_apply, Ideal.mem_inf,
    RingHom.mem_ker, RingHom.mem_ker]

/-- **`I_s ≃ 𝔟_s ⊗ J`.** -/
def eI (s : Finset ι) : Ione (Ch := Ch) E s ≃ₗ[k] Ch.𝔟 s ⊗[k] E.kernel :=
  ((LinearEquiv.ofInjective (mapBJ E s) (mapBJ_injective E s)).trans
    (LinearEquiv.ofEq _ ((Ione E s).restrictScalars k) (by
      ext x; exact (mem_Ione_iff E s x).symm))).symm

/-- `mapBJ` inverts `eI`. -/
theorem mapBJ_eI (s : Finset ι) (x : Ione (Ch := Ch) E s) :
    mapBJ E s (eI E s x) = x := by
  have h := LinearEquiv.apply_symm_apply ((LinearEquiv.ofInjective (mapBJ E s)
    (mapBJ_injective E s)).trans (LinearEquiv.ofEq _ ((Ione E s).restrictScalars k) (by
      ext x; exact (mem_Ione_iff E s x).symm))) x
  exact congrArg Subtype.val h

/-- `eI E s x = w` if and only if `mapBJ E s w = x`. -/
theorem eI_eq_iff (s : Finset ι) (x : Ione (Ch := Ch) E s) (w : Ch.𝔟 s ⊗[k] E.kernel) :
    eI E s x = w ↔ mapBJ E s w = x := by
  constructor
  · rintro rfl
    exact mapBJ_eI E s x
  · exact fun h => mapBJ_injective E s ((mapBJ_eI E s x).trans h.symm)

/-- `mapBJ` takes the action of `a ∈ S_s` to multiplication by `f0 s a ⊗ 1`. -/
theorem mapBJ_smul (s : Finset ι) (a : Ch.S s) (w : Ch.𝔟 s ⊗[k] E.kernel) :
    mapBJ E s (a • w) = (Ch.f0 s a ⊗ₜ 1) * mapBJ E s w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul n j =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy, mul_add]

/-- `id ⊗ (g ∘ f) = (id ⊗ g) ∘ (id ⊗ f)` for algebra maps. -/
theorem algMap_id_comp {X Y Z W : Type u} [CommRing X] [Algebra k X] [CommRing Y]
    [Algebra k Y] [CommRing Z] [Algebra k Z] [CommRing W] [Algebra k W] (f : Y →ₐ[k] Z)
    (g : Z →ₐ[k] W) (x : X ⊗[k] Y) :
    Algebra.TensorProduct.map (AlgHom.id k X) (g.comp f) x =
      Algebra.TensorProduct.map (AlgHom.id k X) g
        (Algebra.TensorProduct.map (AlgHom.id k X) f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The common lift reduces to `f0 ⊗ 1` over the residue field. -/
theorem commonLift_sub_mem (p : CurvePoint Ch A) {s : Finset ι} (hs : s.Nonempty)
    (a : Ch.S s) : commonLift E p hs a - Ch.f0 s a ⊗ₜ 1 ∈
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k (Ch.O s)) (toRes E.big)) := by
  rw [RingHom.mem_ker, map_sub, ← toRes_comp E.π, algMap_id_comp]
  change Algebra.TensorProduct.map (AlgHom.id k (Ch.O s)) (toRes A) (piA E s (commonLift E p hs a))
    - _ = 0
  rw [piA_commonLift, p.pt_res]
  simp

/-- On `Ione E s`, multiplication by the common lift of `a` is multiplication by
`f0 s a ⊗ 1`. -/
theorem mul_mem_Ione_eq (p : CurvePoint Ch A) {s : Finset ι} (hs : s.Nonempty)
    (a : Ch.S s) (x : Ch.O s ⊗[k] E.big.carrier) (hx : x ∈ Ione E s) :
    commonLift E p hs a * x = (Ch.f0 s a ⊗ₜ 1) * x := by
  have hz := commonLift_sub_mem E p hs a
  rw [Algebra.TensorProduct.lTensor_ker _ (fun c => ⟨algebraMap k _ c, (toRes E.big).commutes c⟩)]
    at hz
  have hx' : x ∈ Ideal.map (Algebra.TensorProduct.includeRight :
      E.big.carrier →ₐ[k] Ch.O s ⊗[k] E.big.carrier) (RingHom.ker E.π) := by
    rw [← Algebra.TensorProduct.lTensor_ker _ E.surjective]
    exact (Ideal.mem_inf.1 hx).1
  have hprod := Ideal.mul_mem_mul hz hx'
  rw [← Ideal.map_mul] at hprod
  have h0 : RingHom.ker (toRes E.big) * RingHom.ker E.π = ⊥ := by
    have e1 : RingHom.ker (toRes E.big) = IsLocalRing.maximalIdeal E.big.carrier :=
      ker_algHom_eq_maximalIdeal' (toRes E.big)
    have e2 : RingHom.ker E.π * IsLocalRing.maximalIdeal E.big.carrier = ⊥ :=
      E.ker_mul_maximalIdeal
    rw [e1, mul_comm, e2]
  rw [h0, Ideal.map_bot, Ideal.mem_bot, sub_mul, sub_eq_zero] at hprod
  exact hprod

/-- The scalar actions of `k` and `S_s` on `𝔟_s` commute. -/
instance smulCommB (s : Finset ι) : SMulCommClass k (Ch.S s) (Ch.𝔟 s) :=
  ⟨fun r a n => by
    apply Subtype.ext
    change r • (Ch.f0 s a * (n : Ch.O s)) = Ch.f0 s a * (r • (n : Ch.O s))
    rw [mul_smul_comm]⟩

/-- **The identification `I_s = 𝔟_s ⊗ J` is equivariant** for the action of `S_s` through the
common lift. -/
theorem equivariant_eI (p : CurvePoint Ch A) {s : Finset ι} (hs : s.Nonempty) :
    Cech.IsEquivariantFor ((stageOne E p).φ s hs) (eI E s) := by
  intro a p₀ hp x
  obtain ⟨p', rfl⟩ : ∃ p' : Ch.O s ⊗[k] E.big.carrier, p' = p₀ := ⟨p₀, rfl⟩
  obtain ⟨y₀, hy₀⟩ := x
  obtain ⟨y, rfl⟩ : ∃ y : Ch.O s ⊗[k] E.big.carrier, y = y₀ := ⟨y₀, rfl⟩
  apply mapBJ_injective E s
  erw [mapBJ_eI, mapBJ_smul, mapBJ_eI]
  have h1 : p' - commonLift E p hs a ∈ Ione E s := Ideal.Quotient.eq.1 hp
  have h2 : (p' - commonLift E p hs a) * y = 0 :=
    mul_eq_zero_of_mem_of_mul_eq_bot _ ((stageOne E p).hI s) h1 hy₀
  change p' * y = (Ch.f0 s a ⊗ₜ 1) * y
  rw [← mul_mem_Ione_eq E p hs a y hy₀]
  linear_combination h2

end ThetaOne

section ThetaOneIso

open TensorProduct

variable {k : Type u} [Field k] {ι : Type u} [DecidableEq ι] {Ch : CurveCharts k ι}
  {A : ArtinLocalAlgebra k} (E : SmallExtension A)

/-- `mapBJ` commutes with restriction. -/
theorem mapBJ_rTensor {s t : Finset ι} (h : s ⊆ t) (w : Ch.𝔟 s ⊗[k] E.kernel) :
    mapBJ E t (LinearMap.rTensor E.kernel (Ch.ρB h) w) = ψone E h (mapBJ E s w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul n j => simp; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `ρB h ⊗ id` is semilinear along `σ h`. -/
theorem rTensor_ρB_smul {s t : Finset ι} (h : s ⊆ t) (a : Ch.S s)
    (w : Ch.𝔟 s ⊗[k] E.kernel) :
    LinearMap.rTensor E.kernel (Ch.ρB h) (a • w) =
      Ch.σ h a • LinearMap.rTensor E.kernel (Ch.ρB h) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul n j =>
    rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, Ch.ρB_smul,
      TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- `eI` commutes with restriction. -/
theorem eI_res {s t : Finset ι} (h : s ⊆ t) (x : Ione (Ch := Ch) E s) :
    eI E t ⟨ψone E h x.1, ψone_mem E h x.1 x.2⟩ =
      LinearMap.rTensor E.kernel (Ch.ρB h) (eI E s x) := by
  apply mapBJ_injective E t
  erw [mapBJ_eI, mapBJ_rTensor, mapBJ_eI]

variable (p : CurvePoint Ch A)

/-- Derivations with values in `I_s` are `Der_k(S_s, 𝔟_s ⊗ J)`. -/
def derivEquivDer {s : Finset ι} (hs : s.Nonempty) :
    Deriv (Ione E s) ((stageOne E p).φ s hs) ≃ₗ[k]
      Derivation k (Ch.S s) (Ch.𝔟 s ⊗[k] E.kernel) :=
  Cech.derivEquivDerivation (eI E s) (equivariant_eI E p hs)

/-- `derivEquivDer E p hs D a = eI E s (D a)`. -/
theorem derivEquivDer_apply {s : Finset ι} (hs : s.Nonempty)
    (D : Deriv (Ione E s) ((stageOne E p).φ s hs)) (a : Ch.S s) :
    derivEquivDer E p hs D a = eI E s (D.1 a) := rfl

/-- The tensor identification of derivations. -/
def tensorDer (s : Finset ι) :
    haveI := finite_kernel E
    Derivation k (Ch.S s) (Ch.𝔟 s) ⊗[k] E.kernel ≃ₗ[k]
      Derivation k (Ch.S s) (Ch.𝔟 s ⊗[k] E.kernel) :=
  haveI := finite_kernel E
  Cech.derivationTensorEquiv E.kernel (Module.finBasis k E.kernel)

/-- `tensorDer` intertwines extension of derivations along `σ h` with `ρB h ⊗ id`. -/
theorem tensorDer_extDer {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty)
    (y : Derivation k (Ch.S s) (Ch.𝔟 s) ⊗[k] E.kernel) (a : Ch.S s) :
    tensorDer E t (LinearMap.rTensor E.kernel (Ch.extDerBₗ h hs) y) (Ch.σ h a) =
      LinearMap.rTensor E.kernel (Ch.ρB h) (tensorDer E s y a) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul D j =>
    rw [LinearMap.rTensor_tmul]
    simp only [tensorDer, Cech.derivationTensorEquiv_tmul, LinearMap.rTensor_tmul]
    exact congrArg (· ⊗ₜ[k] j) (Ch.extDerB_apply h hs D a)
  | add x y hx hy => simp only [map_add, Derivation.add_apply, hx, hy]

/-- **Restriction of derivations, in the tensor form.** -/
theorem derivEquivDer_extDeriv {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty)
    (D : Deriv (Ione E s) ((stageOne E p).φ s hs)) :
    haveI := (Ch.toNChartData).smooth s hs
    derivEquivDer E p (hs.mono h) (((stageOne E p).hom h hs).extDeriv (Ch.etale h hs)
      ((stageOne E p).hI s) ((stageOne E p).hI t) D) =
    tensorDer E t (LinearMap.rTensor E.kernel (Ch.extDerBₗ h hs)
      ((tensorDer E s).symm (derivEquivDer E p hs D))) := by
  haveI := (Ch.toNChartData).smooth s hs
  have hδ : ∀ a b, (LinearMap.rTensor E.kernel (Ch.ρB h) ∘ₗ
      (derivEquivDer E p hs D).toLinearMap) (a * b) =
      Ch.σ h a • (LinearMap.rTensor E.kernel (Ch.ρB h) ∘ₗ
        (derivEquivDer E p hs D).toLinearMap) b +
      Ch.σ h b • (LinearMap.rTensor E.kernel (Ch.ρB h) ∘ₗ
        (derivEquivDer E p hs D).toLinearMap) a := by
    intro a b
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe, Derivation.leibniz, map_add,
      rTensor_ρB_smul]
  refine (existsUnique_derivation_etale (Ch.σ h) (Ch.etale h hs) _ hδ).unique (fun a => ?_)
    (fun a => ?_)
  · erw [derivEquivDer_apply]
    have e := ((stageOne E p).hom h hs).extDeriv_apply (Ch.etale h hs) ((stageOne E p).hI s)
      ((stageOne E p).hI t) D a
    have e2 : (((stageOne E p).hom h hs).extDeriv (Ch.etale h hs) ((stageOne E p).hI s)
        ((stageOne E p).hI t) D).1 (Ch.σ h a) = ⟨ψone E h (D.1 a), ψone_mem E h _ (D.1 a).2⟩ :=
      Subtype.ext e
    exact (congrArg (eI E t) e2).trans (eI_res E h (D.1 a))
  · rw [tensorDer_extDer, LinearEquiv.apply_symm_apply]
    rfl

end ThetaOneIso

section ThetaOnePresheaf

open TensorProduct

variable {k : Type u} [Field k] {ι : Type u} [DecidableEq ι] {Ch : CurveCharts k ι}
  {A : ArtinLocalAlgebra k} (E : SmallExtension A) (p : CurvePoint Ch A)

/-- `PLift s.Nonempty` has a unique element when `s` is nonempty. -/
abbrev uniquePLift {s : Finset ι} (hs : s.Nonempty) : Unique (PLift s.Nonempty) :=
  ⟨⟨⟨hs⟩⟩, fun _ => rfl⟩

/-- The component of the identification on a nonempty intersection. -/
def objIsoPos {s : Finset ι} (hs : s.Nonempty) :
    (stageOne E p).derivPresheaf.obj s ≃ₗ[k]
      (Cech.tensorLeft Ch.derivPresheafB E.kernel).obj s :=
  letI := uniquePLift hs
  (LinearEquiv.piUnique k (fun hs' : PLift s.Nonempty =>
      Deriv (Ione E s) ((stageOne E p).φ s hs'.down))).trans
    (((derivEquivDer E p hs).trans ((tensorDer E s).symm.trans (TensorProduct.comm k _ _))).trans
      (LinearEquiv.lTensor E.kernel (LinearEquiv.piUnique k (fun _ : PLift s.Nonempty =>
        Derivation k (Ch.S s) (Ch.𝔟 s))).symm))

/-- The first-stage derivations on the empty intersection form a subsingleton. -/
theorem subsingleton_obj_neg {s : Finset ι} (hs : ¬ s.Nonempty) :
    Subsingleton ((stageOne E p).derivPresheaf.obj s) :=
  ⟨fun x y => funext fun h => absurd h.down hs⟩

/-- `J ⊗ Der(S_s, 𝔟_s)` on the empty intersection is a subsingleton. -/
theorem subsingleton_tensor_neg {s : Finset ι} (hs : ¬ s.Nonempty) :
    Subsingleton ((Cech.tensorLeft Ch.derivPresheafB E.kernel).obj s) := by
  have h0 : ∀ y : Ch.derivPresheafB.obj s, y = 0 := fun y => funext fun h => absurd h.down hs
  refine ⟨fun x y => ?_⟩
  have : ∀ z : E.kernel ⊗[k] Ch.derivPresheafB.obj s, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul j y => rw [h0 y, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact (this x).trans (this y).symm

/-- The component on the empty intersection (both sides are zero). -/
def objIsoNeg {s : Finset ι} (hs : ¬ s.Nonempty) :
    (stageOne E p).derivPresheaf.obj s ≃ₗ[k]
      (Cech.tensorLeft Ch.derivPresheafB E.kernel).obj s :=
  haveI := subsingleton_obj_neg E p hs
  haveI := subsingleton_tensor_neg E (Ch := Ch) hs
  LinearEquiv.ofLinear 0 0 (LinearMap.ext fun _ => Subsingleton.elim _ _)
    (LinearMap.ext fun _ => Subsingleton.elim _ _)

/-- The identification of the derivations of the first stage with `Der(S_s, 𝔟_s) ⊗ J` on each
intersection (zero on the empty one). -/
def objIso (s : Finset ι) :
    (stageOne E p).derivPresheaf.obj s ≃ₗ[k]
      (Cech.tensorLeft Ch.derivPresheafB E.kernel).obj s :=
  if hs : s.Nonempty then objIsoPos E p hs else objIsoNeg E p hs

/-- On a nonempty intersection, `objIso` is `objIsoPos`. -/
theorem objIso_pos {s : Finset ι} (hs : s.Nonempty) (x) :
    objIso E p s x = objIsoPos E p hs x := by
  simp only [objIso, dif_pos hs]

/-- `objIsoPos` is the composite of `derivEquivDer`, the inverse of `tensorDer` and the
commutativity of the tensor product. -/
theorem objIsoPos_apply {s : Finset ι} (hs : s.Nonempty)
    (x : (stageOne E p).derivPresheaf.obj s) :
    letI := uniquePLift hs
    objIsoPos E p hs x = LinearMap.lTensor E.kernel
      (LinearEquiv.piUnique k (fun _ : PLift s.Nonempty =>
        Derivation k (Ch.S s) (Ch.𝔟 s))).symm.toLinearMap
      (TensorProduct.comm k _ _ ((tensorDer E s).symm (derivEquivDer E p hs (x ⟨hs⟩)))) := rfl

/-- On a nonempty `s`, restriction in `derivPresheafB` is `extDerBₗ`. -/
theorem derivPresheafB_res_pos {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty)
    (y : Ch.derivPresheafB.obj s) (ht : PLift t.Nonempty) :
    Ch.derivPresheafB.res h y ht = Ch.extDerBₗ h hs (y ⟨hs⟩) := by
  change (if hs : s.Nonempty then Ch.extDerBₗ h hs (y ⟨hs⟩) else 0) = _
  rw [dif_pos hs]

/-- Extension of derivations along `σ h`, tensored with `J`, is restriction in
`J ⊗ Der(S_·, 𝔟_·)`. -/
theorem tensorRes_aux {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty)
    (y : Derivation k (Ch.S s) (Ch.𝔟 s) ⊗[k] E.kernel) :
    letI := uniquePLift hs
    letI := uniquePLift (hs.mono h)
    LinearMap.lTensor E.kernel (LinearEquiv.piUnique k (fun _ : PLift t.Nonempty =>
        Derivation k (Ch.S t) (Ch.𝔟 t))).symm.toLinearMap
      (TensorProduct.comm k _ _ (LinearMap.rTensor E.kernel (Ch.extDerBₗ h hs) y)) =
    LinearMap.lTensor E.kernel (Ch.derivPresheafB.res h)
      (LinearMap.lTensor E.kernel (LinearEquiv.piUnique k (fun _ : PLift s.Nonempty =>
        Derivation k (Ch.S s) (Ch.𝔟 s))).symm.toLinearMap (TensorProduct.comm k _ _ y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact (map_zero _).symm
  | tmul D j =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.comm_tmul, LinearMap.lTensor_tmul]
    congr 1
    funext ht
    rw [derivPresheafB_res_pos h hs]
    rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (map_add _ _ _).symm

/-- **The presheaf of derivations of the first stage is `J ⊗ Der(S_·, 𝔟_·)`.** -/
def derivIso :
    Cech.Iso (stageOne E p).derivPresheaf (Cech.tensorLeft Ch.derivPresheafB E.kernel) where
  equiv := objIso E p
  map_res {s t} h x := by
    by_cases hs : s.Nonempty
    · have ht : t.Nonempty := hs.mono h
      rw [objIso_pos E p ht, objIso_pos E p hs, objIsoPos_apply, objIsoPos_apply]
      have e1 : ((stageOne E p).derivPresheaf.res h x) ⟨ht⟩ =
          haveI := (Ch.toNChartData).smooth s hs
          ((stageOne E p).hom h hs).extDeriv (Ch.etale h hs) ((stageOne E p).hI s)
            ((stageOne E p).hI t) (x ⟨hs⟩) :=
        NLiftCover.derivRes_apply (stageOne E p) h hs x ⟨ht⟩
      rw [e1]
      erw [derivEquivDer_extDeriv]
      rw [LinearEquiv.symm_apply_apply]
      exact tensorRes_aux E h hs _
    · have hx0 : (stageOne E p).derivPresheaf.res h x = 0 := by
        funext ht
        change (if hs : s.Nonempty then _ else 0) = _
        rw [dif_neg hs]; rfl
      have hy0 : objIso E p s x = 0 := (subsingleton_tensor_neg E hs).elim _ _
      rw [hx0, hy0, map_zero, map_zero]

end ThetaOnePresheaf

section ThetaOneDef

open TensorProduct

variable {k : Type u} [Field k] {ι : Type u} [DecidableEq ι] [Fintype ι] {Ch : CurveCharts k ι}
  {A : ArtinLocalAlgebra k} (E : SmallExtension A) (p : CurvePoint Ch A) {V₁ : Type u}
  [AddCommGroup V₁] [Module k V₁]

/-- **θ₁**: `Ȟ¹` of the first-stage derivations is `V₁ ⊗ J`, given `Ȟ¹(Der(S_·, 𝔟_·)) ≃ V₁`. -/
def thetaOne (θG : Ch.derivPresheafB.H1 ≃ₗ[k] V₁) :
    (stageOne E p).derivPresheaf.H1 ≃ₗ[k] V₁ ⊗[k] E.kernel :=
  ((derivIso E p).h1Equiv.trans (Cech.tensorH1Equiv Ch.derivPresheafB E.kernel).symm).trans
    ((TensorProduct.comm k _ _).trans (TensorProduct.congr θG (LinearEquiv.refl k _)))

variable {E} {E' : SmallExtension A}

/-- `mapBJ` commutes with a quotient map of small extensions. -/
theorem mapBJ_lTensor (q : E.QuotientMap E') {s : Finset ι}
    (w : Ch.𝔟 s ⊗[k] E.kernel) :
    mapBJ E' s (LinearMap.lTensor (Ch.𝔟 s) q.kerMap w) =
      Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom (mapBJ E s w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul n j => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `eI` commutes with a quotient map of small extensions. -/
theorem eI_map (q : E.QuotientMap E') {s : Finset ι} (x : Ione (Ch := Ch) E s) :
    eI E' s ⟨Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom x.1, mapq_mem q x.1 x.2⟩ =
      LinearMap.lTensor (Ch.𝔟 s) q.kerMap (eI E s x) := by
  apply mapBJ_injective E' s
  erw [mapBJ_eI, mapBJ_lTensor, mapBJ_eI]

/-- `tensorDer` commutes with a quotient map of small extensions. -/
theorem tensorDer_lTensor (q : E.QuotientMap E') {s : Finset ι}
    (y : Derivation k (Ch.S s) (Ch.𝔟 s) ⊗[k] E.kernel) (a : Ch.S s) :
    tensorDer E' s (LinearMap.lTensor _ q.kerMap y) a =
      LinearMap.lTensor (Ch.𝔟 s) q.kerMap (tensorDer E s y a) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul D j =>
    rw [LinearMap.lTensor_tmul]
    simp only [tensorDer, Cech.derivationTensorEquiv_tmul, LinearMap.lTensor_tmul]
  | add x y hx hy => simp only [map_add, Derivation.add_apply, hx, hy]

/-- The tensor form of the derivations commutes with a quotient map of small extensions. -/
theorem derivEquivDer_map (q : E.QuotientMap E') {s : Finset ι} (hs : s.Nonempty)
    (D : Deriv (Ione E s) ((stageOne E p).φ s hs)) :
    (tensorDer E' s).symm (derivEquivDer E' p hs
      (((stageOneMap q p).sqHom s hs).mapDerivₗ ((stageOne E' p).hI s) D)) =
    LinearMap.lTensor _ q.kerMap ((tensorDer E s).symm (derivEquivDer E p hs D)) := by
  rw [LinearEquiv.symm_apply_eq]
  refine Derivation.ext fun a => ?_
  rw [tensorDer_lTensor, LinearEquiv.apply_symm_apply]
  erw [derivEquivDer_apply, derivEquivDer_apply]
  exact eI_map q (D.1 a)

/-- `objIso` is natural in the quotients of `J`. -/
theorem objIso_map (q : E.QuotientMap E') (s : Finset ι)
    (x : (stageOne E p).derivPresheaf.obj s) :
    objIso E' p s ((stageOneMap q p).derivHom.map s x) =
      (Cech.tensorMap Ch.derivPresheafB q.kerMap).map s (objIso E p s x) := by
  by_cases hs : s.Nonempty
  · rw [objIso_pos E' p hs, objIso_pos E p hs, objIsoPos_apply, objIsoPos_apply]
    change _ = LinearMap.rTensor _ q.kerMap _
    have e : ((stageOneMap q p).derivHom.map s x) ⟨hs⟩ =
        ((stageOneMap q p).sqHom s hs).mapDerivₗ ((stageOne E' p).hI s) (x ⟨hs⟩) := rfl
    rw [e]
    erw [derivEquivDer_map]
    letI := uniquePLift hs
    have key : ∀ y : Derivation k (Ch.S s) (Ch.𝔟 s) ⊗[k] E.kernel,
        LinearMap.lTensor E'.kernel (LinearEquiv.piUnique k (fun _ : PLift s.Nonempty =>
          Derivation k (Ch.S s) (Ch.𝔟 s))).symm.toLinearMap
          (TensorProduct.comm k _ _ (LinearMap.lTensor _ q.kerMap y)) =
        LinearMap.rTensor _ q.kerMap (LinearMap.lTensor E.kernel (LinearEquiv.piUnique k
          (fun _ : PLift s.Nonempty => Derivation k (Ch.S s) (Ch.𝔟 s))).symm.toLinearMap
          (TensorProduct.comm k _ _ y)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    exact key _
  · have : ∀ z : (Cech.tensorLeft Ch.derivPresheafB E'.kernel).obj s, z = 0 :=
      fun z => (subsingleton_tensor_neg E' hs).elim _ _
    exact (this _).trans (this _).symm

/-- **Naturality of θ₁ in `J`.** -/
theorem thetaOne_map (θG : Ch.derivPresheafB.H1 ≃ₗ[k] V₁) (q : E.QuotientMap E')
    (z : (stageOne E p).derivPresheaf.H1) :
    thetaOne E' p θG ((stageOneMap q p).derivHom.h1 z) =
      LinearMap.lTensor V₁ q.kerMap (thetaOne E p θG z) := by
  have h1 := Cech.Iso.h1Equiv_natural (derivIso E p) (derivIso E' p) (stageOneMap q p).derivHom
    (Cech.tensorMap Ch.derivPresheafB q.kerMap) (fun s x => objIso_map p q s x) z
  set w := (Cech.tensorH1Equiv Ch.derivPresheafB E.kernel).symm ((derivIso E p).h1Equiv z) with hw
  have h2 := Cech.tensorMap_h1_tensorH1Equiv Ch.derivPresheafB q.kerMap w
  rw [hw, LinearEquiv.apply_symm_apply, ← h1] at h2
  have h3 : (Cech.tensorH1Equiv Ch.derivPresheafB E'.kernel).symm
      ((derivIso E' p).h1Equiv ((stageOneMap q p).derivHom.h1 z)) =
      LinearMap.rTensor _ q.kerMap w := by
    rw [h2, LinearEquiv.symm_apply_apply]
  have key : ∀ w' : E.kernel ⊗[k] Ch.derivPresheafB.H1,
      TensorProduct.congr θG (LinearEquiv.refl k E'.kernel)
        (TensorProduct.comm k _ _ (LinearMap.rTensor _ q.kerMap w')) =
      LinearMap.lTensor V₁ q.kerMap
        (TensorProduct.congr θG (LinearEquiv.refl k E.kernel) (TensorProduct.comm k _ _ w')) := by
    intro w'
    induction w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [thetaOne, LinearEquiv.trans_apply]
  rw [h3]
  exact key w

end ThetaOneDef

section StageTwo

open TensorProduct

variable {k : Type u} [Field k] {ι : Type u} [DecidableEq ι] {Ch : CurveCharts k ι}
  {A : ArtinLocalAlgebra k} (E : SmallExtension A)

/-- Restriction maps the kernel of reduction to `A` on `s` into that on `t`. -/
theorem ψone_memK {s t : Finset ι} (h : s ⊆ t) (x : Ch.O s ⊗[k] E.big.carrier)
    (hx : x ∈ RingHom.ker (piA (Ch := Ch) E s)) :
    ψone E h x ∈ RingHom.ker (piA (Ch := Ch) E t) := by
  rw [RingHom.mem_ker] at hx ⊢
  rw [piA_ψone, hx, map_zero]

variable (Ch) in
/-- **The second-stage lifting problem** (over the base): `P_s = O_s ⊗ B`, `I_s = J ⊗ O_s`. -/
def stageTwo : LiftCover.{u} k k ι where
  P s := Ch.O s ⊗[k] E.big.carrier
  I s := RingHom.ker (piA (Ch := Ch) E s)
  hI s := ker_piA_mul E s
  φ s := Algebra.ofId k _
  hom h := SqZeroHom.ofBase _ _ (ψone E h) (ψone_memK E h)
  hom_refl h x := by
    change ψone E h x = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Ch.ρ_refl]
    | add x y hx hy => simp only [map_add, hx, hy]
  hom_comp h₁ h₂ x := by
    change ψone E h₂ (ψone E h₁ x) = ψone E (h₁.trans h₂) x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Ch.ρ_comp]
    | add x y hx hy => simp only [map_add, hx, hy]

variable {E} {E' : SmallExtension A}

/-- A quotient map of small extensions maps the kernel of reduction to `A` into itself. -/
theorem mapq_memK (q : E.QuotientMap E') {s : Finset ι} (x : Ch.O s ⊗[k] E.big.carrier)
    (hx : x ∈ RingHom.ker (piA (Ch := Ch) E s)) :
    Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom x ∈ RingHom.ker (piA (Ch := Ch) E' s) := by
  rw [RingHom.mem_ker] at hx ⊢
  rw [piA_mapq, hx]

variable (Ch) in
/-- The quotient of the second-stage problem along a quotient map. -/
def stageTwoMap (q : E.QuotientMap E') : (stageTwo Ch E).Hom (stageTwo Ch E') where
  sq s := SqZeroHom.ofBase _ _ (Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom)
    (mapq_memK q)
  comm h x := by
    change Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom (ψone E h x) =
      ψone E' h (Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]

variable (E)

/-- The inclusion `O_s ⊗ J → O_s ⊗ B` induced by `J ⊆ B`. -/
abbrev mapOJ (s : Finset ι) : Ch.O s ⊗[k] E.kernel →ₗ[k] Ch.O s ⊗[k] E.big.carrier :=
  LinearMap.lTensor (Ch.O s) E.kernel.subtype

/-- `O_s ⊗ J → O_s ⊗ B` is injective. -/
theorem mapOJ_injective (s : Finset ι) : Function.Injective (mapOJ (Ch := Ch) E s) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ E.kernel.subtype_injective

/-- The kernel of reduction to `A` is the image of `O_s ⊗ J`. -/
theorem mem_K_iff (s : Finset ι) (x : Ch.O s ⊗[k] E.big.carrier) :
    x ∈ RingHom.ker (piA (Ch := Ch) E s) ↔ x ∈ LinearMap.range (mapOJ (Ch := Ch) E s) := by
  rw [RingHom.mem_ker, algMap_id_apply]
  exact ((lTensor_exact (Ch.O s) (exact_kernel E) E.surjective) x)

/-- `I_s = O_s ⊗ J`. -/
def eK (s : Finset ι) : (stageTwo Ch E).idealPresheaf.obj s ≃ₗ[k] Ch.O s ⊗[k] E.kernel :=
  ((LinearEquiv.ofInjective (mapOJ E s) (mapOJ_injective E s)).trans
    (LinearEquiv.ofEq _ ((RingHom.ker (piA (Ch := Ch) E s)).restrictScalars k) (by
      ext x; exact (mem_K_iff E s x).symm))).symm

/-- `mapOJ` inverts `eK`. -/
theorem mapOJ_eK (s : Finset ι) (x : (stageTwo Ch E).idealPresheaf.obj s) :
    mapOJ E s (eK E s x) = x.1 := by
  have h := LinearEquiv.apply_symm_apply ((LinearEquiv.ofInjective (mapOJ E s)
    (mapOJ_injective E s)).trans (LinearEquiv.ofEq _
      ((RingHom.ker (piA (Ch := Ch) E s)).restrictScalars k) (by
      ext x; exact (mem_K_iff E s x).symm))) x
  exact congrArg Subtype.val h

/-- `eK` commutes with restriction. -/
theorem eK_res {s t : Finset ι} (h : s ⊆ t) (x : (stageTwo Ch E).idealPresheaf.obj s) :
    eK E t ((stageTwo Ch E).idealPresheaf.res h x) =
      LinearMap.rTensor E.kernel (Ch.ρ h).toLinearMap (eK E s x) := by
  apply mapOJ_injective E t
  rw [mapOJ_eK]
  have e : ∀ w : Ch.O s ⊗[k] E.kernel, mapOJ E t (LinearMap.rTensor E.kernel (Ch.ρ h).toLinearMap w)
      = ψone E h (mapOJ E s w) := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e, mapOJ_eK]
  rfl

/-- **The presheaf of ideals of the second stage is `J ⊗ O_·`.** -/
def idealIso :
    Cech.Iso (stageTwo Ch E).idealPresheaf (Cech.tensorLeft Ch.ringPresheaf E.kernel) where
  equiv s := (eK E s).trans (TensorProduct.comm k _ _)
  map_res {s t} h x := by
    change TensorProduct.comm k _ _ (eK E t ((stageTwo Ch E).idealPresheaf.res h x)) =
      LinearMap.lTensor E.kernel (Ch.ρ h).toLinearMap (TensorProduct.comm k _ _ (eK E s x))
    rw [eK_res]
    generalize eK E s x = w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

variable [Fintype ι] {V₂ : Type u} [AddCommGroup V₂] [Module k V₂]

/-- **θ₂**: `Ȟ¹` of the second-stage ideals is `V₂ ⊗ J`, given `Ȟ¹(O_·) ≃ V₂`. -/
def thetaTwo (θO : Ch.ringPresheaf.H1 ≃ₗ[k] V₂) :
    (stageTwo Ch E).idealPresheaf.H1 ≃ₗ[k] V₂ ⊗[k] E.kernel :=
  ((idealIso E).h1Equiv.trans (Cech.tensorH1Equiv Ch.ringPresheaf E.kernel).symm).trans
    ((TensorProduct.comm k _ _).trans (TensorProduct.congr θO (LinearEquiv.refl k _)))

variable {E}

/-- `idealIso` is natural in the quotients of `J`. -/
theorem idealIso_map (q : E.QuotientMap E') (s : Finset ι)
    (x : (stageTwo Ch E).idealPresheaf.obj s) :
    (idealIso E').equiv s ((stageTwoMap Ch q).idealHom.map s x) =
      (Cech.tensorMap Ch.ringPresheaf q.kerMap).map s ((idealIso E).equiv s x) := by
  change TensorProduct.comm k _ _ (eK E' s ((stageTwoMap Ch q).idealHom.map s x)) =
    LinearMap.rTensor _ q.kerMap (TensorProduct.comm k _ _ (eK E s x))
  have e1 : eK E' s ((stageTwoMap Ch q).idealHom.map s x) =
      LinearMap.lTensor (Ch.O s) q.kerMap (eK E s x) := by
    apply mapOJ_injective E' s
    rw [mapOJ_eK]
    have e : ∀ w : Ch.O s ⊗[k] E.kernel, mapOJ E' s (LinearMap.lTensor (Ch.O s) q.kerMap w)
        = Algebra.TensorProduct.map (AlgHom.id k _) q.toAlgHom (mapOJ E s w) := fun w => by
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [e, mapOJ_eK]
    rfl
  rw [e1]
  generalize eK E s x = w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Naturality of θ₂ in `J`.** -/
theorem thetaTwo_map (θO : Ch.ringPresheaf.H1 ≃ₗ[k] V₂) (q : E.QuotientMap E')
    (z : (stageTwo Ch E).idealPresheaf.H1) :
    thetaTwo E' θO ((stageTwoMap Ch q).idealHom.h1 z) =
      LinearMap.lTensor V₂ q.kerMap (thetaTwo E θO z) := by
  have h1 := Cech.Iso.h1Equiv_natural (idealIso E) (idealIso E') (stageTwoMap Ch q).idealHom
    (Cech.tensorMap Ch.ringPresheaf q.kerMap) (fun s x => idealIso_map q s x) z
  set w := (Cech.tensorH1Equiv Ch.ringPresheaf E.kernel).symm ((idealIso E).h1Equiv z) with hw
  have h2 := Cech.tensorMap_h1_tensorH1Equiv Ch.ringPresheaf q.kerMap w
  rw [hw, LinearEquiv.apply_symm_apply, ← h1] at h2
  have h3 : (Cech.tensorH1Equiv Ch.ringPresheaf E'.kernel).symm
      ((idealIso E').h1Equiv ((stageTwoMap Ch q).idealHom.h1 z)) =
      LinearMap.rTensor _ q.kerMap w := by
    rw [h2, LinearEquiv.symm_apply_apply]
  have key : ∀ w' : E.kernel ⊗[k] Ch.ringPresheaf.H1,
      TensorProduct.congr θO (LinearEquiv.refl k E'.kernel)
        (TensorProduct.comm k _ _ (LinearMap.rTensor _ q.kerMap w')) =
      LinearMap.lTensor V₂ q.kerMap
        (TensorProduct.congr θO (LinearEquiv.refl k E.kernel) (TensorProduct.comm k _ _ w')) := by
    intro w'
    induction w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [thetaTwo, LinearEquiv.trans_apply]
  rw [h3]
  exact key w

end StageTwo

section Twist

variable {k : Type u} [Field k] {ι : Type u} [DecidableEq ι]

/-- **The second obstruction does not change under twisting by units `≡ 1`.** -/
theorem secondObstruction_twist (C : LiftCover.{u} k k ι)
    {g g' g'' : ∀ i j : ι, (C.P {i, j})ˣ} (hg : C.IsUnitCocycle g) (hg' : C.IsUnitCocycle g')
    (hg'' : C.IsUnitCocycle g'')
    (hc' : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g i j : C.P {i, j}))
    (hc'' : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g'' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g i j : C.P {i, j}))
    (v : ∀ i : ι, (C.P {i})ˣ) (hv : ∀ i, (v i : C.P {i}) - 1 ∈ C.I {i})
    (h : ∀ i j, g'' i j * C.resUnit (CechPresheaf.sub_pair_left i j) (v i) =
      C.resUnit (CechPresheaf.sub_pair_right i j) (v j) * g' i j) :
    C.secondObstruction hg hg'' hc'' = C.secondObstruction hg hg' hc' := by
  unfold LiftCover.secondObstruction
  rw [CechPresheaf.cls_eq_cls_iff]
  refine ⟨fun i => ⟨(v i : C.P {i}) - 1, hv i⟩, ?_⟩
  funext i j
  apply Subtype.ext
  simp only [CechPresheaf.d0, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
  change (C.hom (CechPresheaf.sub_pair_right i j)).ψ ((v j : C.P {j}) - 1) -
      (C.hom (CechPresheaf.sub_pair_left i j)).ψ ((v i : C.P {i}) - 1) =
    ((g'' i j : C.P {i, j}) - g i j) * ((g i j)⁻¹ : (C.P {i, j})ˣ) -
      ((g' i j : C.P {i, j}) - g i j) * ((g i j)⁻¹ : (C.P {i, j})ˣ)
  set I := C.I {i, j}
  have hI := C.hI {i, j}
  set a := (C.hom (CechPresheaf.sub_pair_left i j)).ψ ((v i : C.P {i}) - 1) with ha
  set b := (C.hom (CechPresheaf.sub_pair_right i j)).ψ ((v j : C.P {j}) - 1) with hb
  have haI : a ∈ I := (C.hom _).mem _ (hv i)
  have hbI : b ∈ I := (C.hom _).mem _ (hv j)
  have hres : ∀ (s t : Finset ι) (hst : s ⊆ t) (u : (C.P s)ˣ),
      ((C.resUnit hst u : (C.P t)ˣ) : C.P t) = (C.hom hst).ψ (u : C.P s) := fun s t hst u => by
    simp [LiftCover.resUnit]
  have hvi : ((C.resUnit (CechPresheaf.sub_pair_left i j) (v i) : (C.P {i, j})ˣ) : C.P {i, j}) =
      1 + a := by rw [hres, ha, map_sub, map_one]; ring
  have hvj : ((C.resUnit (CechPresheaf.sub_pair_right i j) (v j) : (C.P {i, j})ˣ) :
      C.P {i, j}) = 1 + b := by rw [hres, hb, map_sub, map_one]; ring
  have H := congrArg Units.val (h i j)
  simp only [Units.val_mul, hvi, hvj] at H
  have hd : (g' i j : C.P {i, j}) - g i j ∈ I := Ideal.Quotient.eq.1 (hc' i j)
  have z1 := mul_eq_zero_of_mem_of_mul_eq_bot I hI haI hd
  have z2 := mul_eq_zero_of_mem_of_mul_eq_bot I hI hbI hd
  have hd'' : (g'' i j : C.P {i, j}) - g i j ∈ I := Ideal.Quotient.eq.1 (hc'' i j)
  have z3 := mul_eq_zero_of_mem_of_mul_eq_bot I hI haI hd''
  have hgg : ((g i j)⁻¹ : (C.P {i, j})ˣ) * (g i j : C.P {i, j}) = 1 := (g i j).inv_mul
  linear_combination (-(((g i j)⁻¹ : (C.P {i, j})ˣ) : C.P {i, j})) * H +
    (((g i j)⁻¹ : (C.P {i, j})ˣ) : C.P {i, j}) * z3 -
    (((g i j)⁻¹ : (C.P {i, j})ˣ) : C.P {i, j}) * z2 - (b - a) * hgg

end Twist

section ChartSystem

open TensorProduct

variable {k : Type u} [Field k] {ι : Type u} [DecidableEq ι] {Ch : CurveCharts k ι}
  {A : ArtinLocalAlgebra k} (E : SmallExtension A) (p : CurvePoint Ch A)

/-- The map underlying a local lift. -/
abbrev toMap {s : Finset ι} (x : (stageOne E p).liftTorsor.X s) :
    Ch.S s →ₐ[k] Ch.O s ⊗[k] E.big.carrier := x.2.1

/-- The map of a restricted local lift is the restriction of the map. -/
theorem toMap_res {s t : Finset ι} (h : s ⊆ t) (x : (stageOne E p).liftTorsor.X s)
    (a : Ch.S s) :
    toMap E p ((stageOne E p).liftTorsor.res h x) (Ch.σ h a) = ψone E h (toMap E p x a) :=
  ((stageOne E p).hom h x.1).extLift_apply (Ch.etale h x.1) ((stageOne E p).hI _) x.2 a

/-- A local lift reduces to the given `A`-point. -/
theorem piA_toMap {s : Finset ι} (x : (stageOne E p).liftTorsor.X s) (a : Ch.S s) :
    piA E s (toMap E p x a) = p.pt s a := by
  have h := x.2.mk_apply a
  have h2 : toMap E p x a - commonLift E p x.1 a ∈ Ione E s := Ideal.Quotient.eq.1 h
  have h3 := RingHom.mem_ker.1 (Ideal.mem_inf.1 h2).1
  rw [map_sub, sub_eq_zero, piA_commonLift] at h3
  exact h3

/-- A local lift is constant on the marked points. -/
theorem piB_toMap {s : Finset ι} (x : (stageOne E p).liftTorsor.X s) (a : Ch.S s) :
    piB E s (toMap E p x a) = fixB E s a := by
  have h := x.2.mk_apply a
  have h2 : toMap E p x a - commonLift E p x.1 a ∈ Ione E s := Ideal.Quotient.eq.1 h
  have h3 := RingHom.mem_ker.1 (Ideal.mem_inf.1 h2).2
  rw [map_sub, sub_eq_zero, piB_commonLift] at h3
  exact h3

/-- In a compatible family, the extensions to an intersection agree. -/
theorem res_eq_of_compat (y : ∀ i : ι, (stageOne E p).liftTorsor.X {i})
    (hy : ∀ i j : ι, (stageOne E p).liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
      (stageOne E p).liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j))
    {s : Finset ι} {i j : ι} (hi : {i} ⊆ s) (hj : {j} ⊆ s) :
    (stageOne E p).liftTorsor.res hi (y i) = (stageOne E p).liftTorsor.res hj (y j) := by
  have hij : ({i, j} : Finset ι) ⊆ s := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hi (Finset.mem_singleton_self _)
    · obtain rfl := Finset.mem_singleton.1 hz
      exact hj (Finset.mem_singleton_self _)
  rw [← (stageOne E p).liftTorsor.res_comp (CechPresheaf.sub_pair_left i j) hij,
    ← (stageOne E p).liftTorsor.res_comp (CechPresheaf.sub_pair_right i j) hij, hy i j]

end ChartSystem

section ChartSystemDef

open TensorProduct

/-- **The chart system of the curve map at `[f]`**: the charts (`CurveCharts`), the Čech
comparisons `θG`, `θO` with the obstruction spaces, the coordinates `x` of the target charts
(`x m i = T_m / T_{l i}`) with transition units `t`, local expressions `w` of the basis of
`H⁰(C, L)` in trivializations of `L` with transition functions `g`, gluing of sections over
Artinian bases, the points of `R` on the charts with their coefficients and frames, and the
universal property of `R` for tuples satisfying the closed conditions. -/
structure ChartSystem (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    (V₁ V₂ : Type u) [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    (d N : ℕ) where
  /-- The index type of the cover. -/
  ι : Type u
  [fin : Fintype ι]
  [dec : DecidableEq ι]
  /-- The charts of the curve map. -/
  Ch : CurveCharts k ι
  /-- The identification `Ȟ¹(Der(S_·, 𝔟_·)) ≃ V₁`. -/
  θG : Ch.derivPresheafB.H1 ≃ₗ[k] V₁
  /-- The identification `Ȟ¹(O_·) ≃ V₂`. -/
  θO : Ch.ringPresheaf.H1 ≃ₗ[k] V₂
  /-- The index `l i` of the coordinate that is `1` on the chart `i`. -/
  l : ι → Fin (d + 1)
  /-- The coordinates `x m i = T_m / T_{l i}` of the target chart `i`. -/
  x : Fin (d + 1) → ∀ i : ι, Ch.S {i}
  /-- The coordinate `x (l i) i` is `1`. -/
  x_self : ∀ i, x (l i) i = 1
  /-- The transition units of the target charts. -/
  t : ∀ i j : ι, (Ch.S {i, j})ˣ
  /-- The coordinates change by the transition units `t`. -/
  x_trans : ∀ m i j, Ch.σ (CechPresheaf.sub_pair_left i j) (x m i) =
    t i j * Ch.σ (CechPresheaf.sub_pair_right i j) (x m j)
  /-- The transition units `t` form a cocycle. -/
  t_cocycle : ∀ i j l', Ch.σ (CechPresheaf.pair_sub_triple₁₂ i j l') (t i j) *
    Ch.σ (CechPresheaf.pair_sub_triple₂₃ i j l') (t j l') =
      Ch.σ (CechPresheaf.pair_sub_triple₁₃ i j l') (t i l')
  /-- The local expressions on the chart `i` of the basis of `H⁰(C, L)`. -/
  w : ∀ i : ι, Fin N → Ch.O {i}
  /-- The transition functions of `L`. -/
  g : ∀ i j : ι, (Ch.O {i, j})ˣ
  /-- The transition functions `g` form a cocycle. -/
  g_cocycle : ∀ i j l', Ch.ρ (CechPresheaf.pair_sub_triple₁₂ i j l') (g i j) *
    Ch.ρ (CechPresheaf.pair_sub_triple₂₃ i j l') (g j l') =
      Ch.ρ (CechPresheaf.pair_sub_triple₁₃ i j l') (g i l')
  /-- The local expressions `w` change by the transition functions `g`. -/
  w_trans : ∀ i j m, Ch.ρ (CechPresheaf.sub_pair_left i j) (w i m) =
    g i j * Ch.ρ (CechPresheaf.sub_pair_right i j) (w j m)
  /-- Local sections over `B` compatible under `g` are combinations of the `w` with coefficients
  in `B`. -/
  glue : ∀ (B : ArtinLocalAlgebra k) (u : ∀ i : ι, Ch.O {i} ⊗[k] B.carrier),
    (∀ i j, Algebra.TensorProduct.map (Ch.ρ (CechPresheaf.sub_pair_left i j)) (AlgHom.id k _)
      (u i) = ((g i j : Ch.O {i, j}) ⊗ₜ[k] (1 : B.carrier)) *
        Algebra.TensorProduct.map (Ch.ρ (CechPresheaf.sub_pair_right i j)) (AlgHom.id k _)
          (u j)) →
    ∃ c : Fin N → B.carrier, ∀ i, u i = ∑ m, w i m ⊗ₜ[k] c m
  /-- The coefficients of the gluing are unique. -/
  glue_unique : ∀ (B : ArtinLocalAlgebra k) (c : Fin N → B.carrier),
    (∀ i, ∑ m, w i m ⊗ₜ[k] c m = 0) → c = 0
  /-- The `A`-point of the curve map on the charts given by an `A`-point of `R`. -/
  pt : ∀ {A : ArtinLocalAlgebra k}, (R →ₐ[k] A.carrier) → CurvePoint Ch A
  /-- The coefficients of an `A`-point of `R`. -/
  coeff : ∀ {A : ArtinLocalAlgebra k}, (R →ₐ[k] A.carrier) → Fin (d + 1) → Fin N → A.carrier
  /-- On each chart a unit frame relates the coefficients to the coordinates of the point. -/
  frame : ∀ {A : ArtinLocalAlgebra k} (a : R →ₐ[k] A.carrier) (i : ι),
    ∃ fr : (Ch.O {i} ⊗[k] A.carrier)ˣ, ∀ m,
      ∑ j, w i j ⊗ₜ[k] coeff a m j = fr * (pt a).pt {i} (x m i)
  /-- The linear form normalizing the coefficients. -/
  μ : Fin (d + 1) → Fin N → k
  /-- The coefficients of every point are normalized by `μ`. -/
  μ_coeff : ∀ {A : ArtinLocalAlgebra k} (a : R →ₐ[k] A.carrier),
    ∑ m, ∑ j, algebraMap k A.carrier (μ m j) * coeff a m j = 1
  /-- The closed conditions on a tuple of coefficients. -/
  Good : ∀ B : ArtinLocalAlgebra k, (Fin (d + 1) → Fin N → B.carrier) → Prop
  /-- Coefficients given locally by maps fixed on the marked points and frames, and normalized by
  `μ`, satisfy the closed conditions. -/
  good_of_local : ∀ (B : ArtinLocalAlgebra k) (c : Fin (d + 1) → Fin N → B.carrier)
    (y : ∀ i : ι, Ch.S {i} →ₐ[k] Ch.O {i} ⊗[k] B.carrier)
    (fr : ∀ i : ι, (Ch.O {i} ⊗[k] B.carrier)ˣ),
    (∀ i m, ∑ j, w i j ⊗ₜ[k] c m j = fr i * y i (x m i)) →
    (∀ i z, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ch.𝔟 {i})) (AlgHom.id k _) (y i z) =
      Ideal.Quotient.mk _ (Ch.f0 {i} z) ⊗ₜ[k] 1) →
    ∑ m, ∑ j, algebraMap k B.carrier (μ m j) * c m j = 1 → Good B c
  /-- The universal property of `R`: coefficients over `B` lifting those of `a` and satisfying the
  closed conditions give a lift of `a`. -/
  lift : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier)
    (c : Fin (d + 1) → Fin N → E.big.carrier),
    (∀ m j, E.π (c m j) = coeff a m j) → Good E.big c → ∃ b : R →ₐ[k] E.big.carrier, E.π.comp b = a

attribute [instance] ChartSystem.fin ChartSystem.dec

end ChartSystemDef

section Assemble

open TensorProduct

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {V₁ V₂ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] {d N : ℕ}
  (CS : ChartSystem k R V₁ V₂ d N) {A : ArtinLocalAlgebra k} (E : SmallExtension A)
  (a : R →ₐ[k] A.carrier)

/-- A unit over `A` lifts to a unit over `B`. -/
theorem exists_unit_lift {s : Finset CS.ι} (u : (CS.Ch.O s ⊗[k] A.carrier)ˣ) :
    ∃ F : (CS.Ch.O s ⊗[k] E.big.carrier)ˣ,
      piA (Ch := CS.Ch) E s (F : CS.Ch.O s ⊗[k] E.big.carrier) = u := by
  obtain ⟨F, hF⟩ := piA_surjective (Ch := CS.Ch) E s (u : CS.Ch.O s ⊗[k] A.carrier)
  obtain ⟨G, hG⟩ := piA_surjective (Ch := CS.Ch) E s
    (((u⁻¹ : (CS.Ch.O s ⊗[k] A.carrier)ˣ)) : CS.Ch.O s ⊗[k] A.carrier)
  have hn : F * G - 1 ∈ RingHom.ker (piA (Ch := CS.Ch) E s) := by
    rw [RingHom.mem_ker, map_sub, map_mul, hF, hG, map_one, Units.mul_inv, sub_self]
  have hsq := mul_eq_zero_of_mem_of_mul_eq_bot _ (ker_piA_mul E s) hn hn
  have hunit : IsUnit (F * G) := by
    refine ⟨⟨F * G, 1 - (F * G - 1), ?_, ?_⟩, rfl⟩
    · linear_combination (-1 : CS.Ch.O s ⊗[k] E.big.carrier) * hsq
    · linear_combination (-1 : CS.Ch.O s ⊗[k] E.big.carrier) * hsq
  exact ⟨(isUnit_of_mul_isUnit_left hunit).unit, hF⟩

/-- The chosen frame over `A`. -/
def frA (i : CS.ι) : (CS.Ch.O {i} ⊗[k] A.carrier)ˣ := (CS.frame a i).choose

/-- The chosen frame over `A` relates the coefficients to the coordinates of the point. -/
theorem frA_spec (i : CS.ι) (m : Fin (d + 1)) :
    ∑ j, CS.w i j ⊗ₜ[k] CS.coeff a m j = (frA CS a i : _) * (CS.pt a).pt {i} (CS.x m i) :=
  (CS.frame a i).choose_spec m

/-- The chosen frame over `B`. -/
def frB (i : CS.ι) : (CS.Ch.O {i} ⊗[k] E.big.carrier)ˣ :=
  (exists_unit_lift CS E (frA CS a i)).choose

/-- The chosen frame over `B` reduces to the chosen frame over `A`. -/
theorem piA_frB (i : CS.ι) :
    piA (Ch := CS.Ch) E {i} (frB CS E a i : CS.Ch.O {i} ⊗[k] E.big.carrier) = frA CS a i :=
  (exists_unit_lift CS E (frA CS a i)).choose_spec

end Assemble

section Assemble2

open TensorProduct

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {V₁ V₂ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] {d N : ℕ}
  (CS : ChartSystem k R V₁ V₂ d N) {A : ArtinLocalAlgebra k} (E : SmallExtension A)
  (a : R →ₐ[k] A.carrier)

/-- In a commutative group, `a b = c` gives `(a y x⁻¹)(b z y⁻¹) = c z x⁻¹`. -/
theorem cocycle_aux {G : Type*} [CommGroup G] (a b c x y z : G) (hc : a * b = c) :
    (a * y * x⁻¹) * (b * z * y⁻¹) = c * z * x⁻¹ := by
  rw [← hc]
  calc (a * y * x⁻¹) * (b * z * y⁻¹) = (a * b * z * x⁻¹) * (y * y⁻¹) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel, mul_one]

/-- The restriction of a unit of the second stage is its image under `ψone`. -/
theorem resUnit_val {s t : Finset CS.ι} (h : s ⊆ t) (u : ((stageTwo CS.Ch E).P s)ˣ) :
    (((stageTwo CS.Ch E).resUnit h u : ((stageTwo CS.Ch E).P t)ˣ) : (stageTwo CS.Ch E).P t) =
      ψone E h (u : (stageTwo CS.Ch E).P s) := rfl

/-- `ψone` is transitive. -/
theorem ψone_comp_apply {s t v : Finset CS.ι} (h₁ : s ⊆ t) (h₂ : t ⊆ v)
    (x : CS.Ch.O s ⊗[k] E.big.carrier) : ψone E h₂ (ψone E h₁ x) = ψone E (h₁.trans h₂) x :=
  (stageTwo CS.Ch E).hom_comp h₁ h₂ x

/-- The fixed transition function `g_ij ⊗ 1`. -/
def gB (i j : CS.ι) : ((stageTwo CS.Ch E).P {i, j})ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : CS.Ch.O {i, j} →ₐ[k] _).toMonoidHom (CS.g i j)

/-- The underlying element of `gB CS E i j` is `g i j ⊗ 1`. -/
theorem gB_val (i j : CS.ι) :
    ((gB CS E i j : ((stageTwo CS.Ch E).P {i, j})ˣ) : (stageTwo CS.Ch E).P {i, j}) =
      ((CS.g i j : CS.Ch.O {i, j}) ⊗ₜ[k] (1 : E.big.carrier) : CS.Ch.O {i, j} ⊗[k] E.big.carrier) :=
  rfl

/-- **The reference transition functions** `g_ij F_j / F_i` of `L_B` relative to frames `F`. -/
def refU (F : ∀ i : CS.ι, ((stageTwo CS.Ch E).P {i})ˣ) (i j : CS.ι) :
    ((stageTwo CS.Ch E).P {i, j})ˣ :=
  gB CS E i j * (stageTwo CS.Ch E).resUnit (CechPresheaf.sub_pair_right i j) (F j) *
    ((stageTwo CS.Ch E).resUnit (CechPresheaf.sub_pair_left i j) (F i))⁻¹

/-- `refU F i j · F_i = g_ij · F_j`. -/
theorem refU_mul (F : ∀ i : CS.ι, ((stageTwo CS.Ch E).P {i})ˣ) (i j : CS.ι) :
    refU CS E F i j * (stageTwo CS.Ch E).resUnit (CechPresheaf.sub_pair_left i j) (F i) =
      gB CS E i j * (stageTwo CS.Ch E).resUnit (CechPresheaf.sub_pair_right i j) (F j) := by
  rw [refU, inv_mul_cancel_right]

/-- Restriction of units is transitive. -/
theorem resUnit_comp {s t v : Finset CS.ι} (h₁ : s ⊆ t) (h₂ : t ⊆ v)
    (u : ((stageTwo CS.Ch E).P s)ˣ) :
    (stageTwo CS.Ch E).resUnit h₂ ((stageTwo CS.Ch E).resUnit h₁ u) =
      (stageTwo CS.Ch E).resUnit (h₁.trans h₂) u :=
  Units.ext (ψone_comp_apply CS E h₁ h₂ _)

/-- The fixed transition functions `gB` form a cocycle. -/
theorem gB_cocycle (i j l : CS.ι) :
    (stageTwo CS.Ch E).resUnit (CechPresheaf.pair_sub_triple₁₂ i j l) (gB CS E i j) *
      (stageTwo CS.Ch E).resUnit (CechPresheaf.pair_sub_triple₂₃ i j l) (gB CS E j l) =
    (stageTwo CS.Ch E).resUnit (CechPresheaf.pair_sub_triple₁₃ i j l) (gB CS E i l) := by
  apply Units.ext
  rw [Units.val_mul, resUnit_val, resUnit_val, resUnit_val, gB_val, gB_val, gB_val]
  simp only [ψone, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).trans (by rw [mul_one, CS.g_cocycle i j l])

/-- The reference transition functions form a cocycle. -/
theorem isUnitCocycle_refU (F : ∀ i : CS.ι, ((stageTwo CS.Ch E).P {i})ˣ) :
    (stageTwo CS.Ch E).IsUnitCocycle (refU CS E F) := by
  intro i j l
  have hc := gB_cocycle CS E i j l
  simp only [refU, map_mul, map_inv, resUnit_comp]
  exact cocycle_aux _ _ _ _ _ _ hc

end Assemble2

section Assemble3

open TensorProduct

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {V₁ V₂ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] {d N : ℕ}
  (CS : ChartSystem k R V₁ V₂ d N) {A : ArtinLocalAlgebra k} (E : SmallExtension A)
  (a : R →ₐ[k] A.carrier)

/-- The local maps of a family of local lifts, extended to `U_s`. -/
abbrev Ys (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i}) {s : Finset CS.ι}
    {i : CS.ι} (hi : {i} ⊆ s) : CS.Ch.S s →ₐ[k] CS.Ch.O s ⊗[k] E.big.carrier :=
  toMap E (CS.pt a) ((stageOne E (CS.pt a)).liftTorsor.res hi (y i))

/-- `Ys` commutes with restriction. -/
theorem Ys_res (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i})
    {s t : Finset CS.ι} {i : CS.ι} (hi : {i} ⊆ s) (h : s ⊆ t) (z : CS.Ch.S s) :
    ψone E h (Ys CS E a y hi z) = Ys CS E a y (hi.trans h) (CS.Ch.σ h z) := by
  rw [← toMap_res]
  unfold Ys
  rw [(stageOne E (CS.pt a)).liftTorsor.res_comp]

/-- For a compatible family, `Ys` does not depend on the chosen chart `i` with `{i} ⊆ s`. -/
theorem Ys_indep (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i})
    (hy : ∀ i j : CS.ι,
      (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
        (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j))
    {s : Finset CS.ι} {i j : CS.ι} (hi : {i} ⊆ s) (hj : {j} ⊆ s) :
    Ys CS E a y hi = Ys CS E a y hj := by
  unfold Ys
  rw [res_eq_of_compat E (CS.pt a) y hy hi hj]

/-- On the chart `i` itself, `Ys` is the map of the local lift `y i`. -/
theorem Ys_self (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i}) (i : CS.ι)
    (h : ({i} : Finset CS.ι) ⊆ {i}) : Ys CS E a y h = toMap E (CS.pt a) (y i) := by
  unfold Ys
  rw [(stageOne E (CS.pt a)).liftTorsor.res_refl]

/-- **The pulled-back transition functions** `Y(t_ij)` of `𝒪(1)` along the glued lift. -/
def pullU (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i}) (i j : CS.ι) :
    ((stageTwo CS.Ch E).P {i, j})ˣ :=
  Units.map (Ys CS E a y (CechPresheaf.sub_pair_left i j)).toMonoidHom (CS.t i j)

/-- The underlying element of `pullU` is `Y(t_ij)`. -/
theorem pullU_val (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i}) (i j : CS.ι) :
    ((pullU CS E a y i j : ((stageTwo CS.Ch E).P {i, j})ˣ) : (stageTwo CS.Ch E).P {i, j}) =
      Ys CS E a y (CechPresheaf.sub_pair_left i j) (CS.t i j : CS.Ch.S {i, j}) := rfl

/-- For a compatible family, the pulled-back transition functions form a cocycle. -/
theorem isUnitCocycle_pullU (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i})
    (hy : ∀ i j : CS.ι,
      (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
        (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j)) :
    (stageTwo CS.Ch E).IsUnitCocycle (pullU CS E a y) := by
  intro i j l
  apply Units.ext
  rw [Units.val_mul, resUnit_val, resUnit_val, resUnit_val, pullU_val, pullU_val, pullU_val]
  change ψone E _ (Ys CS E a y _ _) * ψone E _ (Ys CS E a y _ _) = ψone E _ (Ys CS E a y _ _)
  rw [Ys_res, Ys_res, Ys_res,
    Ys_indep CS E a y hy ((CechPresheaf.sub_pair_left j l).trans
      (CechPresheaf.pair_sub_triple₂₃ i j l))
      ((CechPresheaf.sub_pair_left i j).trans (CechPresheaf.pair_sub_triple₁₂ i j l)),
    Ys_indep CS E a y hy ((CechPresheaf.sub_pair_left i l).trans
      (CechPresheaf.pair_sub_triple₁₃ i j l))
      ((CechPresheaf.sub_pair_left i j).trans (CechPresheaf.pair_sub_triple₁₂ i j l))]
  exact (map_mul _ _ _).symm.trans (congrArg _ (CS.t_cocycle i j l))

end Assemble3

section Assemble4

open TensorProduct

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {V₁ V₂ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] {d N : ℕ}
  (CS : ChartSystem k R V₁ V₂ d N) {A : ArtinLocalAlgebra k} (E : SmallExtension A)
  (a : R →ₐ[k] A.carrier)

/-- `f ⊗ id` applied to `∑ m, w m ⊗ c m` is `∑ m, f (w m) ⊗ c m`. -/
theorem map_sum_tmul {B : Type u} [CommRing B] [Algebra k B] {s t : Finset CS.ι}
    (f : CS.Ch.O s →ₐ[k] CS.Ch.O t) (w : Fin N → CS.Ch.O s) (c : Fin N → B) :
    Algebra.TensorProduct.map f (AlgHom.id k B) (∑ m, w m ⊗ₜ[k] c m) = ∑ m, f (w m) ⊗ₜ[k] c m := by
  simp [map_sum]

/-- `(g r) ⊗ c = (g ⊗ 1)(r ⊗ c)`. -/
theorem mul_tmul_eq {B : Type u} [CommRing B] [Algebra k B] {s : Finset CS.ι}
    (g r : CS.Ch.O s) (c : B) : (g * r) ⊗ₜ[k] c = (g ⊗ₜ[k] (1 : B)) * (r ⊗ₜ[k] c) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **The frames over `A` intertwine the transition functions**: `fr_i · Y(t_ij) = g_ij · fr_j`. -/
theorem frame_trans (i j : CS.ι) :
    Algebra.TensorProduct.map (CS.Ch.ρ (CechPresheaf.sub_pair_left i j)) (AlgHom.id k A.carrier)
        (frA CS a i : CS.Ch.O {i} ⊗[k] A.carrier) * (CS.pt a).pt {i, j} (CS.t i j) =
      ((CS.g i j : CS.Ch.O {i, j}) ⊗ₜ[k] (1 : A.carrier)) *
        Algebra.TensorProduct.map (CS.Ch.ρ (CechPresheaf.sub_pair_right i j))
          (AlgHom.id k A.carrier) (frA CS a j : CS.Ch.O {j} ⊗[k] A.carrier) := by
  have hj := frA_spec CS a j (CS.l j)
  rw [CS.x_self, map_one, mul_one] at hj
  have hi := congrArg (Algebra.TensorProduct.map (CS.Ch.ρ (CechPresheaf.sub_pair_left i j))
    (AlgHom.id k A.carrier)) (frA_spec CS a i (CS.l j))
  rw [map_mul, ← (CS.pt a).pt_comm, CS.x_trans, CS.x_self, map_one, mul_one,
    map_sum_tmul] at hi
  rw [← hi, ← hj, map_sum_tmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [CS.w_trans, mul_tmul_eq]

end Assemble4

section Assemble5

open TensorProduct

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {V₁ V₂ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] {d N : ℕ}
  (CS : ChartSystem k R V₁ V₂ d N) {A : ArtinLocalAlgebra k} (E : SmallExtension A)
  (a : R →ₐ[k] A.carrier)

/-- Frames over `B` lifting the frames over `A`. -/
abbrev IsFrameLift (F : ∀ i : CS.ι, ((stageTwo CS.Ch E).P {i})ˣ) : Prop :=
  ∀ i, piA (Ch := CS.Ch) E {i} ((F i : (stageTwo CS.Ch E).P {i}) : CS.Ch.O {i} ⊗[k] E.big.carrier) =
    frA CS a i

/-- The chosen frame lift. -/
def frLift : ∀ i : CS.ι, ((stageTwo CS.Ch E).P {i})ˣ := fun i => frB CS E a i

/-- The chosen frame lift lifts the frames over `A`. -/
theorem isFrameLift_frLift : IsFrameLift CS E a (frLift CS E a) := fun i => piA_frB CS E a i

/-- **The reference and pulled-back transition functions agree over `A`.** -/
theorem mk_refU_eq (F : ∀ i : CS.ι, ((stageTwo CS.Ch E).P {i})ˣ)
    (hF : IsFrameLift CS E a F) (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i})
    (i j : CS.ι) :
    Ideal.Quotient.mk ((stageTwo CS.Ch E).I {i, j})
        ((refU CS E F i j : ((stageTwo CS.Ch E).P {i, j})ˣ) : (stageTwo CS.Ch E).P {i, j}) =
      Ideal.Quotient.mk ((stageTwo CS.Ch E).I {i, j})
        ((pullU CS E a y i j : ((stageTwo CS.Ch E).P {i, j})ˣ) : (stageTwo CS.Ch E).P {i, j}) := by
  rw [Ideal.Quotient.eq]
  set rv : CS.Ch.O {i, j} ⊗[k] E.big.carrier :=
    ((refU CS E F i j : (stageTwo CS.Ch E).P {i, j}) : CS.Ch.O {i, j} ⊗[k] E.big.carrier) with hrv
  set pv : CS.Ch.O {i, j} ⊗[k] E.big.carrier :=
    ((pullU CS E a y i j : (stageTwo CS.Ch E).P {i, j}) : CS.Ch.O {i, j} ⊗[k] E.big.carrier)
    with hpv
  obtain ⟨fi, hfi⟩ : ∃ x : CS.Ch.O {i} ⊗[k] E.big.carrier,
      x = ((F i : (stageTwo CS.Ch E).P {i}) : CS.Ch.O {i} ⊗[k] E.big.carrier) := ⟨_, rfl⟩
  obtain ⟨fj, hfj⟩ : ∃ x : CS.Ch.O {j} ⊗[k] E.big.carrier,
      x = ((F j : (stageTwo CS.Ch E).P {j}) : CS.Ch.O {j} ⊗[k] E.big.carrier) := ⟨_, rfl⟩
  have hFi : piA (Ch := CS.Ch) E {i} fi = frA CS a i := hfi ▸ hF i
  have hFj : piA (Ch := CS.Ch) E {j} fj = frA CS a j := hfj ▸ hF j
  have h1 : rv * ψone E (CechPresheaf.sub_pair_left i j) fi =
      ((CS.g i j : CS.Ch.O {i, j}) ⊗ₜ[k] (1 : E.big.carrier)) *
        ψone E (CechPresheaf.sub_pair_right i j) fj := by
    rw [hfi, hfj]
    exact congrArg Units.val (refU_mul CS E F i j)
  have h1' := congrArg (piA (Ch := CS.Ch) E {i, j}) h1
  rw [map_mul, map_mul, piA_ψone, piA_ψone, hFi, hFj] at h1'
  have h2 := frame_trans CS a i j
  have hp : piA (Ch := CS.Ch) E {i, j} pv = (CS.pt a).pt {i, j} (CS.t i j) :=
    piA_toMap E (CS.pt a) _ _
  have hu : IsUnit (Algebra.TensorProduct.map (CS.Ch.ρ (CechPresheaf.sub_pair_left i j))
      (AlgHom.id k A.carrier) (frA CS a i : CS.Ch.O {i} ⊗[k] A.carrier)) :=
    (frA CS a i).isUnit.map _
  have key : piA (Ch := CS.Ch) E {i, j} rv = piA (Ch := CS.Ch) E {i, j} pv := by
    rw [hp]
    refine hu.mul_right_cancel ?_
    rw [mul_comm ((CS.pt a).pt {i, j} (CS.t i j)), h2, h1']
    simp
  exact RingHom.mem_ker.2 ((map_sub _ _ _).trans (sub_eq_zero.2 key))

end Assemble5

section Swap

variable {k : Type u} [Field k] {ι : Type u} [DecidableEq ι]

/-- Exchanging the two cocycles negates the second obstruction. -/
theorem secondObstruction_swap (C : LiftCover.{u} k k ι)
    {g g' : ∀ i j : ι, (C.P {i, j})ˣ} (hg : C.IsUnitCocycle g) (hg' : C.IsUnitCocycle g')
    (hc : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g i j : C.P {i, j})) :
    C.secondObstruction hg' hg (fun i j => (hc i j).symm) = - C.secondObstruction hg hg' hc := by
  rw [eq_neg_iff_add_eq_zero]
  unfold LiftCover.secondObstruction
  change C.idealPresheaf.cls _ _ + C.idealPresheaf.cls _ _ = 0
  have hsum : C.idealPresheaf.IsCocycle
      (C.ratioCochain g' g (fun i j => (hc i j).symm) + C.ratioCochain g g' hc) :=
    (C.idealPresheaf.Z1).add_mem (C.isCocycle_ratioCochain hg' hg _)
      (C.isCocycle_ratioCochain hg hg' hc)
  have e : C.idealPresheaf.cls _ (C.isCocycle_ratioCochain hg' hg (fun i j => (hc i j).symm)) +
      C.idealPresheaf.cls _ (C.isCocycle_ratioCochain hg hg' hc) =
      C.idealPresheaf.cls _ hsum := rfl
  rw [e, CechPresheaf.cls_eq_zero_iff]
  refine ⟨0, ?_⟩
  rw [map_zero]
  funext i j
  apply Subtype.ext
  simp only [Pi.add_apply, Pi.zero_apply, LiftCover.ratioCochain, unitRatio]
  change (0 : C.P {i, j}) = (((g i j : C.P {i, j}) - g' i j) * ((g' i j)⁻¹ : (C.P {i, j})ˣ) +
    ((g' i j : C.P {i, j}) - g i j) * ((g i j)⁻¹ : (C.P {i, j})ˣ))
  have hd : (g' i j : C.P {i, j}) - g i j ∈ C.I {i, j} := Ideal.Quotient.eq.1 (hc i j)
  have z := mul_eq_zero_of_mem_of_mul_eq_bot _ (C.hI {i, j}) hd hd
  have h1 : ((g' i j)⁻¹ : (C.P {i, j})ˣ) * (g' i j : C.P {i, j}) = 1 := (g' i j).inv_mul
  have h2 : ((g i j)⁻¹ : (C.P {i, j})ˣ) * (g i j : C.P {i, j}) = 1 := (g i j).inv_mul
  linear_combination (-((((g' i j)⁻¹ : (C.P {i, j})ˣ) : C.P {i, j}) *
    (((g i j)⁻¹ : (C.P {i, j})ˣ) : C.P {i, j}))) * z +
    (((g' i j : C.P {i, j}) - g i j) * (((g i j)⁻¹ : (C.P {i, j})ˣ) : C.P {i, j})) * h1 -
    (((g' i j : C.P {i, j}) - g i j) * (((g' i j)⁻¹ : (C.P {i, j})ˣ) : C.P {i, j})) * h2

end Swap

section Assemble6

open TensorProduct

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {V₁ V₂ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] {d N : ℕ}
  (CS : ChartSystem k R V₁ V₂ d N) {A : ArtinLocalAlgebra k} (E : SmallExtension A)
  (a : R →ₐ[k] A.carrier)

/-- In a commutative group, `(g x p⁻¹)(p q⁻¹) = (x y⁻¹)(g y q⁻¹)`. -/
theorem twist_aux {G : Type*} [CommGroup G] (g x y p q : G) :
    (g * x * p⁻¹) * (p * q⁻¹) = (x * y⁻¹) * (g * y * q⁻¹) := by
  calc (g * x * p⁻¹) * (p * q⁻¹) = (g * x * q⁻¹) * (p⁻¹ * p) := by ac_rfl
    _ = (g * x * q⁻¹) * (y⁻¹ * y) := by rw [inv_mul_cancel, inv_mul_cancel]
    _ = _ := by ac_rfl

/-- If two units have the same reduction to `A`, then `u v⁻¹ - 1` lies in the kernel of the
reduction. -/
theorem mul_inv_sub_one_mem {i : CS.ι} (u v : (CS.Ch.O {i} ⊗[k] E.big.carrier)ˣ)
    (h : piA (Ch := CS.Ch) E {i} (u : CS.Ch.O {i} ⊗[k] E.big.carrier) =
      piA (Ch := CS.Ch) E {i} (v : CS.Ch.O {i} ⊗[k] E.big.carrier)) :
    ((u * v⁻¹ : (CS.Ch.O {i} ⊗[k] E.big.carrier)ˣ) : CS.Ch.O {i} ⊗[k] E.big.carrier) - 1 ∈
      RingHom.ker (piA (Ch := CS.Ch) E {i}) := by
  rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero, Units.val_mul, map_mul, h, ← map_mul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]

/-- The second obstruction class for frame lifts `F`. -/
def obsClass (F : ∀ i : CS.ι, ((stageTwo CS.Ch E).P {i})ˣ) (hF : IsFrameLift CS E a F)
    (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i})
    (hy : ∀ i j : CS.ι,
      (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
        (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j)) :
    (stageTwo CS.Ch E).idealPresheaf.H1 :=
  (stageTwo CS.Ch E).secondObstruction (isUnitCocycle_refU CS E F) (isUnitCocycle_pullU CS E a y hy)
    (fun i j => (mk_refU_eq CS E a F hF y i j).symm)

/-- The second obstruction class does not depend on the frame lifts. -/
theorem obsClass_indep (F F' : ∀ i : CS.ι, ((stageTwo CS.Ch E).P {i})ˣ)
    (hF : IsFrameLift CS E a F) (hF' : IsFrameLift CS E a F')
    (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i})
    (hy : ∀ i j : CS.ι,
      (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
        (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j)) :
    obsClass CS E a F hF y hy = obsClass CS E a F' hF' y hy := by
  unfold obsClass
  have e1 := secondObstruction_swap (stageTwo CS.Ch E) (isUnitCocycle_refU CS E F)
    (isUnitCocycle_pullU CS E a y hy) (fun i j => (mk_refU_eq CS E a F hF y i j).symm)
  have e2 := secondObstruction_swap (stageTwo CS.Ch E) (isUnitCocycle_refU CS E F')
    (isUnitCocycle_pullU CS E a y hy) (fun i j => (mk_refU_eq CS E a F' hF' y i j).symm)
  have e1' := congrArg Neg.neg e1
  have e2' := congrArg Neg.neg e2
  rw [neg_neg] at e1' e2'
  rw [← e1', ← e2']
  congr 1
  refine secondObstruction_twist (stageTwo CS.Ch E) _ _ _ _ _ (fun i => F i * (F' i)⁻¹)
    (fun i => ?_) (fun i j => ?_)
  · exact mul_inv_sub_one_mem CS E (F i) (F' i) ((hF i).trans (hF' i).symm)
  · simp only [refU, map_mul, map_inv]
    exact twist_aux _ _ _ _ _

/-- **The second obstruction of a compatible family of local lifts**, in `V₂ ⊗ J`. -/
def obsTwo (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i})
    (hy : ∀ i j : CS.ι,
      (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
        (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j)) :
    V₂ ⊗[k] E.kernel :=
  thetaTwo E CS.θO (obsClass CS E a (frLift CS E a) (isFrameLift_frLift CS E a) y hy)

end Assemble6

section Assemble7

open TensorProduct

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {V₁ V₂ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] {d N : ℕ}
  (CS : ChartSystem k R V₁ V₂ d N) {A : ArtinLocalAlgebra k} {E : SmallExtension A}
  (a : R →ₐ[k] A.carrier)

/-- The second obstruction is natural in the quotients of `J`. -/
theorem obsTwo_map {E' : SmallExtension A} (q : E.QuotientMap E')
    (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i})
    (hy : ∀ i j : CS.ι,
      (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
        (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j))
    (hy' : ∀ i j : CS.ι, (stageOne E' (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_left i j)
        ((stageOneMap q (CS.pt a)).liftHom.map _ (y i)) =
      (stageOne E' (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_right i j)
        ((stageOneMap q (CS.pt a)).liftHom.map _ (y j))) :
    obsTwo CS E' a (fun i => (stageOneMap q (CS.pt a)).liftHom.map _ (y i)) hy' =
      LinearMap.lTensor V₂ q.kerMap (obsTwo CS E a y hy) := by
  unfold obsTwo
  rw [← thetaTwo_map]
  congr 1
  let F' : ∀ i : CS.ι, ((stageTwo CS.Ch E').P {i})ˣ :=
    fun i => (stageTwoMap CS.Ch q).mapUnit {i} (frLift CS E a i)
  have hF' : IsFrameLift CS E' a F' := fun i =>
    (piA_mapq (Ch := CS.Ch) q (s := {i}) _).trans (isFrameLift_frLift CS E a i)
  rw [obsClass_indep CS E' a (frLift CS E' a) F' (isFrameLift_frLift CS E' a) hF']
  unfold obsClass
  rw [LiftCover.Hom.secondObstruction_map]
  refine LiftCover.secondObstruction_congr _ ?_ ?_ _ _ _ _ _ _
  · funext i j
    have hg : (stageTwoMap CS.Ch q).mapUnit {i, j} (gB CS E i j) = gB CS E' i j := by
      apply Units.ext
      change Algebra.TensorProduct.map (AlgHom.id k (CS.Ch.O {i, j})) q.toAlgHom
        ((CS.g i j : CS.Ch.O {i, j}) ⊗ₜ[k] (1 : E.big.carrier)) = _
      simp; rfl
    simp only [refU, map_mul, map_inv, LiftCover.Hom.resUnit_mapUnit, hg, F']
  · funext i j
    apply Units.ext
    change Ys CS E' a _ _ _ = Algebra.TensorProduct.map (AlgHom.id k (CS.Ch.O {i, j})) q.toAlgHom
      (Ys CS E a y _ _)
    unfold Ys
    rw [← (stageOneMap q (CS.pt a)).liftHom.map_res]
    rfl

end Assemble7

section Assemble8

open TensorProduct

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {V₁ V₂ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] {d N : ℕ}
  (CS : ChartSystem k R V₁ V₂ d N) {A : ArtinLocalAlgebra k} (E : SmallExtension A)
  (a : R →ₐ[k] A.carrier)

/-- In a commutative group, `p e_i = e_j (g f_j f_i⁻¹)` gives `(f_i e_i) p = g (f_j e_j)`. -/
theorem frame_aux {G : Type*} [CommGroup G] (p ei ej g fi fj : G)
    (h : p * ei = ej * (g * fj * fi⁻¹)) : (fi * ei) * p = g * (fj * ej) := by
  calc (fi * ei) * p = fi * (p * ei) := by ac_rfl
    _ = fi * (ej * (g * fj * fi⁻¹)) := by rw [h]
    _ = g * (fj * ej) * (fi * fi⁻¹) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel, mul_one]

/-- **Gluing the frames**: from an isomorphism of the transition functions, frames `Φ_i` over `B`
with `Φ_i Y(t_ij) = g_ij Φ_j`, lifting the frames over `A`. -/
theorem exists_glued_frames
    (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i})
    (hy : ∀ i j : CS.ι,
      (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
        (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j))
    (h0 : obsTwo CS E a y hy = 0) :
    ∃ Φ : ∀ i : CS.ι, (CS.Ch.O {i} ⊗[k] E.big.carrier)ˣ,
      (∀ i, piA (Ch := CS.Ch) E {i} (Φ i : CS.Ch.O {i} ⊗[k] E.big.carrier) = frA CS a i) ∧
      ∀ i j, ψone E (CechPresheaf.sub_pair_left i j) (Φ i : CS.Ch.O {i} ⊗[k] E.big.carrier) *
          Ys CS E a y (CechPresheaf.sub_pair_left i j) (CS.t i j : CS.Ch.S {i, j}) =
        ((CS.g i j : CS.Ch.O {i, j}) ⊗ₜ[k] (1 : E.big.carrier)) *
          ψone E (CechPresheaf.sub_pair_right i j) (Φ j : CS.Ch.O {j} ⊗[k] E.big.carrier) := by
  have h1 : obsClass CS E a (frLift CS E a) (isFrameLift_frLift CS E a) y hy = 0 :=
    (thetaTwo E CS.θO).injective (by rwa [map_zero])
  obtain ⟨e, he1, he2⟩ := (stageTwo CS.Ch E).exists_iso_of_secondObstruction_eq_zero _ _ _ h1
  refine ⟨fun i => frLift CS E a i * e i, fun i => ?_, fun i j => ?_⟩
  · obtain ⟨ev, hev⟩ : ∃ x : CS.Ch.O {i} ⊗[k] E.big.carrier,
        x = ((e i : (stageTwo CS.Ch E).P {i}) : CS.Ch.O {i} ⊗[k] E.big.carrier) := ⟨_, rfl⟩
    obtain ⟨fv, hfv⟩ : ∃ x : CS.Ch.O {i} ⊗[k] E.big.carrier,
        x = ((frLift CS E a i : (stageTwo CS.Ch E).P {i}) : CS.Ch.O {i} ⊗[k] E.big.carrier) :=
      ⟨_, rfl⟩
    have hm : piA (Ch := CS.Ch) E {i} ev = 1 := by
      have := he1 i
      rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at this
      have h' : ev - 1 ∈ RingHom.ker (piA (Ch := CS.Ch) E {i}) := by rwa [hev]
      rwa [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h'
    have hf : piA (Ch := CS.Ch) E {i} fv = frA CS a i := by
      rw [hfv]
      exact isFrameLift_frLift CS E a i
    have : piA (Ch := CS.Ch) E {i} (fv * ev) = frA CS a i := by rw [map_mul, hm, mul_one, hf]
    rwa [hfv, hev] at this
  · have key := frame_aux _ _ _ _ _ _ (he2 i j)
    simp only [← map_mul] at key
    exact congrArg Units.val key

end Assemble8

section Assemble9

open TensorProduct

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {V₁ V₂ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] {d N : ℕ}
  (CS : ChartSystem k R V₁ V₂ d N) {A : ArtinLocalAlgebra k} (E : SmallExtension A)
  (a : R →ₐ[k] A.carrier)

/-- For a compatible family, the images of the coordinates change by `Y(t_ij)`. -/
theorem ψone_toMap_x (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i})
    (hy : ∀ i j : CS.ι,
      (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
        (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j))
    (m : Fin (d + 1)) (i j : CS.ι) :
    ψone E (CechPresheaf.sub_pair_left i j) (toMap E (CS.pt a) (y i) (CS.x m i)) =
      Ys CS E a y (CechPresheaf.sub_pair_left i j) (CS.t i j : CS.Ch.S {i, j}) *
        ψone E (CechPresheaf.sub_pair_right i j) (toMap E (CS.pt a) (y j) (CS.x m j)) := by
  rw [← Ys_self CS E a y i (Finset.Subset.refl _), ← Ys_self CS E a y j (Finset.Subset.refl _),
    Ys_res, Ys_res, CS.x_trans, map_mul,
    Ys_indep CS E a y hy ((Finset.Subset.refl _).trans (CechPresheaf.sub_pair_right i j))
      (CechPresheaf.sub_pair_left i j)]

/-- `∑ j, w j ⊗ (b c j) = (1 ⊗ b) ∑ j, w j ⊗ c j`. -/
theorem tmul_sum_mul {s : Finset CS.ι} (b : E.big.carrier) (w : Fin N → CS.Ch.O s)
    (c : Fin N → E.big.carrier) :
    ∑ j, w j ⊗ₜ[k] (b * c j) = ((1 : CS.Ch.O s) ⊗ₜ[k] b) * ∑ j, w j ⊗ₜ[k] c j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- Reduction to `A` of `∑ j, w j ⊗ c j` is `∑ j, w j ⊗ π (c j)`. -/
theorem piA_sum {s : Finset CS.ι} (w : Fin N → CS.Ch.O s) (c : Fin N → E.big.carrier) :
    piA (Ch := CS.Ch) E s (∑ j, w j ⊗ₜ[k] c j) = ∑ j, w j ⊗ₜ[k] E.π (c j) := by
  simp [map_sum]

/-- **A compatible family with vanishing second obstruction lifts the point.** -/
theorem lift_of_obsTwo (y : ∀ i : CS.ι, (stageOne E (CS.pt a)).liftTorsor.X {i})
    (hy : ∀ i j : CS.ι,
      (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
        (stageOne E (CS.pt a)).liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j))
    (h0 : obsTwo CS E a y hy = 0) : ∃ b : R →ₐ[k] E.big.carrier, E.π.comp b = a := by
  classical
  obtain ⟨Φ, hΦA, hΦ⟩ := exists_glued_frames CS E a y hy h0
  let Y : ∀ i : CS.ι, CS.Ch.S {i} →ₐ[k] CS.Ch.O {i} ⊗[k] E.big.carrier :=
    fun i => toMap E (CS.pt a) (y i)
  have hglue : ∀ m i j, Algebra.TensorProduct.map (CS.Ch.ρ (CechPresheaf.sub_pair_left i j))
      (AlgHom.id k E.big.carrier) ((Φ i : CS.Ch.O {i} ⊗[k] E.big.carrier) * Y i (CS.x m i)) =
      ((CS.g i j : CS.Ch.O {i, j}) ⊗ₜ[k] (1 : E.big.carrier)) *
        Algebra.TensorProduct.map (CS.Ch.ρ (CechPresheaf.sub_pair_right i j))
          (AlgHom.id k E.big.carrier)
            ((Φ j : CS.Ch.O {j} ⊗[k] E.big.carrier) * Y j (CS.x m j)) := by
    intro m i j
    change ψone E _ (_ * _) = _ * ψone E _ (_ * _)
    rw [map_mul, map_mul, ψone_toMap_x CS E a y hy m i j, ← mul_assoc, hΦ i j, mul_assoc]
  choose c' hc' using fun m => CS.glue E.big (fun i => (Φ i : CS.Ch.O {i} ⊗[k] E.big.carrier) *
    Y i (CS.x m i)) (hglue m)
  have hπc : ∀ m j, E.π (c' m j) = CS.coeff a m j := by
    intro m
    have hz := CS.glue_unique A (fun j => E.π (c' m j) - CS.coeff a m j) (fun i => by
      simp only [TensorProduct.tmul_sub, Finset.sum_sub_distrib]
      rw [sub_eq_zero, ← piA_sum, ← hc' m i, map_mul, hΦA, frA_spec]
      exact congrArg _ (piA_toMap E (CS.pt a) (y i) (CS.x m i)))
    intro j
    exact sub_eq_zero.1 (congrFun hz j)
  set ν : E.big.carrier := ∑ m, ∑ j, algebraMap k E.big.carrier (CS.μ m j) * c' m j with hν
  have hπν : E.π ν = 1 := by
    rw [hν, ← CS.μ_coeff a]
    simp only [map_sum, map_mul, AlgHom.commutes, hπc]
  have hνu : IsUnit ν := by
    by_contra hne
    have hm : ν ∈ IsLocalRing.maximalIdeal E.big.carrier :=
      (IsLocalRing.mem_maximalIdeal _).2 hne
    rw [← ker_algHom_eq_maximalIdeal' (toRes E.big), RingHom.mem_ker] at hm
    have : toRes E.big ν = 1 := by
      rw [← toRes_comp E.π, AlgHom.comp_apply, hπν, map_one]
    exact one_ne_zero (this.symm.trans hm)
  set νi : E.big.carrier := ((hνu.unit⁻¹ : E.big.carrierˣ) : E.big.carrier) with hνi
  have hνiν : νi * ν = 1 := hνu.unit.inv_mul
  have hπνi : E.π νi = 1 := by
    have := congrArg E.π hνiν
    rwa [map_mul, hπν, mul_one, map_one] at this
  refine CS.lift E a (fun m j => νi * c' m j) (fun m j => by rw [map_mul, hπνi, one_mul, hπc])
    (CS.good_of_local E.big _ Y (fun i => Φ i * Units.map
      (Algebra.TensorProduct.includeRight :
        E.big.carrier →ₐ[k] CS.Ch.O {i} ⊗[k] E.big.carrier).toMonoidHom
        hνu.unit⁻¹) (fun i m => ?_) (fun i z => piB_toMap E (CS.pt a) (y i) z) ?_)
  · rw [tmul_sum_mul, ← hc' m i]
    have e : ((Units.map (Algebra.TensorProduct.includeRight : E.big.carrier →ₐ[k]
        CS.Ch.O {i} ⊗[k] E.big.carrier).toMonoidHom hνu.unit⁻¹ :
          (CS.Ch.O {i} ⊗[k] E.big.carrier)ˣ) : CS.Ch.O {i} ⊗[k] E.big.carrier) =
        (1 : CS.Ch.O {i}) ⊗ₜ[k] νi := rfl
    rw [Units.val_mul, e]
    ring
  · simp only [mul_left_comm _ νi, ← Finset.mul_sum]
    rw [← hν, hνiν]

end Assemble9

section Final

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {V₁ V₂ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] {d N : ℕ}

/-- The marked deformation data of a chart system. -/
def ChartSystem.toData (CS : ChartSystem k R V₁ V₂ d N) :
    MarkedDeformationData k R CS.ι V₁ V₂ where
  F₁ E a := (stageOne E (CS.pt a)).derivPresheaf
  T₁ E a := (stageOne E (CS.pt a)).liftTorsor
  nonempty₁ E a i := (stageOne E (CS.pt a)).nonempty_X i
  mapF₁ q a := (stageOneMap q (CS.pt a)).derivHom
  mapT₁ q a := (stageOneMap q (CS.pt a)).liftHom
  θ₁ E a := thetaOne E (CS.pt a) CS.θG
  θ₁_map q a z := thetaOne_map (CS.pt a) CS.θG q z
  obs₂ E a y hy := obsTwo CS E a y hy
  obs₂_map q a y hy hy' := obsTwo_map CS a q y hy hy'
  lift_of_obs E a y hy h := lift_of_obsTwo CS E a y hy h

/-- **A chart system gives a two-stage obstruction theory.** -/
theorem nonempty_theory_of_chartSystem (CS : ChartSystem k R V₁ V₂ d N) :
    Nonempty (TwoStageObstructionTheory.{u, u, u} k R V₁ V₂) :=
  ⟨CS.toData.toTheory⟩

end Final

end ChartDeformations

end MMP.Fourfold.CurveChartDeformations

end

end
