module
public import MMP.AlgebraicGeometry.Analytic.CornerPresentation
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.WeightedSurfaceIdentity
public import MMP.AlgebraicGeometry.Analytic.SchemeManifoldDescent
public import MMP.AlgebraicTopology.NerveTheorem

/-!
# Finite homotopy type of a projective complex scheme

Let `X` be a projective scheme over `ℂ`, and let `X^an` be its set of complex points with the
analytic topology. Then `X^an` is homotopy equivalent to a finite polyhedron, that is, to the
underlying space of a simplicial complex with finitely many faces in some Euclidean space
`ℝ^N`.

The proof is a Noetherian induction over the closed subsets `Z ⊆ X`: the `ℂ`-points of `X` over
`Z` have the homotopy type of a finite polyhedron. The reduced closed subscheme `Y` on `Z` is
projective, and its singular locus `S` contains no irreducible component of `Y`: the local ring
at the generic point of a component of a reduced scheme is a field, hence regular, hence a
smooth point over the perfect field `ℂ`. So `S` maps onto a strictly smaller closed subset of
`X`. The corner presentation writes `Y^an` as the pushout `M ∪_{∂M} S^an` of a finite disjoint
union of compact manifolds with corners along its boundary, and `M`, `∂M` and `S^an` have
finite polyhedral models (the compact-corner lemma and the induction hypothesis).

The boundary has a collar, which absorbs the cylinder of the double mapping cylinder
`D(∂M ⊆ M, φ)`, so the pushout is homeomorphic to it. Double mapping cylinders are invariant,
up to homotopy equivalence, under homotopies of the attaching maps and under homotopy
equivalences of the two ends and of the middle; every such map is of the form `phi` (a path in
one end, then the cylinder, then a path in the other end), a composite of two such maps is one
such map after a reparametrization of the cylinder, and the homotopies between them are
continuous families of their data. The ends are replaced by realizations of abstract simplicial
complexes in coordinate spaces, and the middle by the cubical form of such a realization. The
grid subdivision of mesh `1/m` of the cubical realization, with multilinear tent weights, is
homotopy equivalent to the realization of a simplicial complex on the grid points: the
barycentric combination of grid points inverts the weights exactly, and the other composite is
a straight-line homotopy in a face. For `m` beyond a Lebesgue number of the cover by preimages
of open stars, every grid vertex goes to vertices whose open stars contain the images of its
star; this gives simplicial approximations of the two attaching maps. The double mapping
cylinder of two simplicial maps `β`, `γ` is homotopy equivalent to the realization of the
complex of joins `τ * σ` and `σ * τ'` of the simplices `σ` with simplices containing `β σ`,
`γ σ`, whose open vertex stars form a good cover; the nerve theorem gives the finite
polyhedron.

## Main results

* `MMP.Analytic.exists_homotopyEquiv_finite_simplicialComplex_of_isProjective`: the finite
  polyhedron homotopy model of `X^an`.

## Implementation notes

* A finite polyhedron is the space `Geometry.SimplicialComplex.space` of a
  `Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))` whose set of faces is finite. This is
  the convention of `MMP.exists_collar_and_homotopyEquiv_finite_simplicialComplex`. The homotopy
  equivalence is a `ContinuousMap.HomotopyEquiv`. The space `X^an` is
  `MMP.Analytic.ComplexPoints.analyticSpace sX`, where `sX : X ⟶ Spec ℂ` is the structure
  morphism. Projectivity is `AlgebraicGeometry.IsProjective sX`. No reducedness is assumed:
  nilpotents do not change `X^an`.
* The induction is over the closed subsets of `X`, well-founded because a projective scheme over
  `ℂ` is Noetherian, rather than over the dimension: the image of the singular locus of the
  reduced subscheme on `Z` is a proper closed subset of `Z` whenever `Z` is nonempty.
* Simplicial approximation is carried out on the cubical realization
  `{u ∈ [0,1]^V | some u_v = 1, supp u ⊆ σ ∈ S}`, homeomorphic to the simplicial realization by
  rescaling; its grid points of mesh `1/m` within distance `< 1/m` of a point `u` span a face,
  so the multilinear tent weights give an explicit simplicial model.
* The homotopy invariance of double mapping cylinders is proved from one-sided inverses: the
  map induced by a homotopy equivalence of an end has an explicit left inverse, and it agrees,
  up to a homotopy of attaching maps, with a map having a left inverse in the other direction.
* The auxiliary lemmas of the proof live in the namespace
  `MMP.FiniteHomotopyType`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002]
-/

open Set Function Topology

namespace MMP.FiniteHomotopyType

section DmcPart

open unitInterval

noncomputable section

/-- Clamp a real number into the unit interval. -/
private def cl (x : ℝ) : I := Set.projIcc 0 1 zero_le_one x

private lemma continuous_cl : Continuous cl := continuous_projIcc (h := zero_le_one)

private lemma coe_cl {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : (cl x : ℝ) = x := by
  simp [cl, Set.projIcc_of_mem _ ⟨h0, h1⟩]

private lemma cl_coe (t : I) : cl t = t := Set.projIcc_val zero_le_one t

private lemma cl_of_le {x : ℝ} (h : x ≤ 0) : cl x = 0 := by
  simp [cl, Set.projIcc_of_le_left _ h]

private lemma cl_of_ge {x : ℝ} (h : 1 ≤ x) : cl x = 1 := by
  simp [cl, Set.projIcc_of_right_le _ h]

private lemma cl_zero : cl 0 = 0 := cl_of_le le_rfl
private lemma cl_one : cl 1 = 1 := cl_of_ge le_rfl

variable {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

private inductive DRel (f : C → A) (g : C → B) : A ⊕ B ⊕ (C × I) → A ⊕ B ⊕ (C × I) → Prop
  | left (c : C) : DRel f g (.inr (.inr (c, 0))) (.inl (f c))
  | right (c : C) : DRel f g (.inr (.inr (c, 1))) (.inr (.inl (g c)))

/-- The double mapping cylinder `A ∪_f (C × I) ∪_g B`. -/
private abbrev DMC (f : C → A) (g : C → B) : Type _ := Quot (DRel f g)

namespace DMC

variable {f : C → A} {g : C → B}

private def inA (a : A) : DMC f g := Quot.mk _ (.inl a)
private def inB (b : B) : DMC f g := Quot.mk _ (.inr (.inl b))
private def cyl (c : C) (t : I) : DMC f g := Quot.mk _ (.inr (.inr (c, t)))

private lemma cyl_zero (c : C) : (cyl c 0 : DMC f g) = inA (f c) := Quot.sound (.left c)
private lemma cyl_one (c : C) : (cyl c 1 : DMC f g) = inB (g c) := Quot.sound (.right c)

private lemma ind {P : DMC f g → Prop} (hA : ∀ a, P (inA a)) (hB : ∀ b, P (inB b))
    (hC : ∀ c t, P (cyl c t)) (x : DMC f g) : P x := by
  induction x using Quot.ind with
  | mk p =>
    rcases p with a | b | ⟨c, t⟩
    · exact hA a
    · exact hB b
    · exact hC c t

private lemma continuous_inA : Continuous (inA : A → DMC f g) :=
  continuous_quot_mk.comp continuous_inl
private lemma continuous_inB : Continuous (inB : B → DMC f g) :=
  continuous_quot_mk.comp (continuous_inr.comp continuous_inl)
private lemma continuous_cyl : Continuous (fun p : C × I ↦ (cyl p.1 p.2 : DMC f g)) :=
  continuous_quot_mk.comp (continuous_inr.comp continuous_inr)

/-- A map out of the double mapping cylinder, from its restrictions to the three pieces. -/
private def desc {Y : Type*} (uA : A → Y) (uB : B → Y) (w : C → I → Y)
    (h0 : ∀ c, w c 0 = uA (f c)) (h1 : ∀ c, w c 1 = uB (g c)) : DMC f g → Y :=
  Quot.lift (Sum.elim uA (Sum.elim uB fun p ↦ w p.1 p.2)) (by
    rintro _ _ (⟨c⟩ | ⟨c⟩)
    · simp [h0]
    · simp [h1])

section desc

variable {Y : Type*} {uA : A → Y} {uB : B → Y} {w : C → I → Y}
  {h0 : ∀ c, w c 0 = uA (f c)} {h1 : ∀ c, w c 1 = uB (g c)}

@[local simp] private lemma desc_inA (a : A) : desc uA uB w h0 h1 (inA a) = uA a := rfl
@[local simp] private lemma desc_inB (b : B) : desc uA uB w h0 h1 (inB b) = uB b := rfl
@[local simp] private lemma desc_cyl (c : C) (t : I) : desc uA uB w h0 h1 (cyl c t) = w c t := rfl

private lemma continuous_desc [TopologicalSpace Y] (hA : Continuous uA) (hB : Continuous uB)
    (hw : Continuous fun p : C × I ↦ w p.1 p.2) : Continuous (desc uA uB w h0 h1) :=
  continuous_quot_lift _ (hA.sumElim (hB.sumElim hw))

end desc

attribute [local simp] desc_inA desc_inB desc_cyl

/-- Continuity of a map on `I × DMC f g` can be checked on the three pieces. -/
private lemma continuous_of_prod {Y : Type*} [TopologicalSpace Y] {F : I × DMC f g → Y}
    (hA : Continuous fun p : I × A ↦ F (p.1, inA p.2))
    (hB : Continuous fun p : I × B ↦ F (p.1, inB p.2))
    (hC : Continuous fun p : I × (C × I) ↦ F (p.1, cyl p.2.1 p.2.2)) : Continuous F := by
  refine isQuotientMap_quot_mk.continuous_lift_prod_right ?_
  have h1 : Continuous fun p : I × (B ⊕ C × I) ↦ F (p.1, Quot.mk _ (.inr p.2)) := by
    have := (hB.sumElim hC).comp
      (Homeomorph.prodSumDistrib (X := I) (Y := B) (Z := C × I)).continuous
    refine this.congr ?_
    rintro ⟨s, b | ⟨c, t⟩⟩ <;> rfl
  have := (hA.sumElim h1).comp
    (Homeomorph.prodSumDistrib (X := I) (Y := A) (Z := B ⊕ C × I)).continuous
  refine this.congr ?_
  rintro ⟨s, a | p⟩ <;> rfl

/-- A homotopy from an explicit continuous function on `I × X`. -/
private lemma homotopic_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {F₀ F₁ : C(X, Y)} (F : I × X → Y) (hF : Continuous F) (h0 : ∀ x, F (0, x) = F₀ x)
    (h1 : ∀ x, F (1, x) = F₁ x) : F₀.Homotopic F₁ :=
  ⟨{ toFun := F, continuous_toFun := hF, map_zero_left := h0, map_one_left := h1 }⟩

section Phi

variable {A' B' C' : Type*} [TopologicalSpace A'] [TopologicalSpace B'] [TopologicalSpace C']
  {f' : C' → A'} {g' : C' → B'}

/-- The cylinder part of `phi`: a path in `A'`, then the cylinder over `γ`, then a path in
`B'`. -/
private def phiW (γ : C → C') (H : C → I → A') (K : C → I → B') (c : C) (t : I) :
    DMC f' g' :=
  if (t : ℝ) ≤ 1 / 3 then inA (H c (cl (3 * t)))
  else if (t : ℝ) ≤ 2 / 3 then cyl (γ c) (cl (3 * t - 1)) else inB (K c (cl (3 - 3 * t)))

private lemma phiW_of_le {γ : C → C'} {H : C → I → A'} {K : C → I → B'} {c : C} {t : I}
    (h : (t : ℝ) ≤ 1 / 3) : (phiW γ H K c t : DMC f' g') = inA (H c (cl (3 * t))) := by
  unfold phiW; rw [if_pos h]

private lemma phiW_of_mid {γ : C → C'} {H : C → I → A'} {K : C → I → B'} {c : C} {t : I}
    (h1 : 1 / 3 < (t : ℝ)) (h2 : (t : ℝ) ≤ 2 / 3) :
    (phiW γ H K c t : DMC f' g') = cyl (γ c) (cl (3 * t - 1)) := by
  unfold phiW; rw [if_neg (not_le.2 h1), if_pos h2]

private lemma phiW_of_gt {γ : C → C'} {H : C → I → A'} {K : C → I → B'} {c : C} {t : I}
    (h : 2 / 3 < (t : ℝ)) : (phiW γ H K c t : DMC f' g') = inB (K c (cl (3 - 3 * t))) := by
  have h' : ¬ (t : ℝ) ≤ 1 / 3 := by linarith
  unfold phiW; rw [if_neg h', if_neg (not_le.2 h)]

/-- The map `D(f, g) → D(f', g')` induced by maps `α, β, γ` of the three pieces and homotopies
`H : α ∘ f ≃ f' ∘ γ`, `K : β ∘ g ≃ g' ∘ γ`. -/
private def phi (α : A → A') (β : B → B') (γ : C → C') (H : C → I → A') (K : C → I → B')
    (hH0 : ∀ c, H c 0 = α (f c)) (hK0 : ∀ c, K c 0 = β (g c))
    (hH1 : ∀ c, H c 1 = f' (γ c)) (hK1 : ∀ c, K c 1 = g' (γ c)) : DMC f g → DMC f' g' :=
  desc (fun a ↦ inA (α a)) (fun b ↦ inB (β b)) (phiW γ H K)
    (fun c ↦ by rw [phiW_of_le (by simp)]; simp [cl_zero, hH0])
    (fun c ↦ by rw [phiW_of_gt (by norm_num)]; norm_num [cl_zero, hK0])

section

variable {α : A → A'} {β : B → B'} {γ : C → C'} {H : C → I → A'} {K : C → I → B'}
  {hH0 : ∀ c, H c 0 = α (f c)} {hK0 : ∀ c, K c 0 = β (g c)}
  {hH1 : ∀ c, H c 1 = f' (γ c)} {hK1 : ∀ c, K c 1 = g' (γ c)}

@[local simp] private lemma phi_inA (a : A) :
    phi α β γ H K hH0 hK0 hH1 hK1 (inA a) = inA (α a) := rfl
@[local simp] private lemma phi_inB (b : B) :
    phi α β γ H K hH0 hK0 hH1 hK1 (inB b) = inB (β b) := rfl
@[local simp] private lemma phi_cyl (c : C) (t : I) :
    phi α β γ H K hH0 hK0 hH1 hK1 (cyl c t) = phiW γ H K c t := rfl

end

/-- `phi` depends only on the values of its data. -/
private lemma phi_congr {α α₁ : A → A'} {β β₁ : B → B'} {γ γ₁ : C → C'} {H H₁ : C → I → A'}
    {K K₁ : C → I → B'} {hH0 : ∀ c, H c 0 = α (f c)} {hK0 : ∀ c, K c 0 = β (g c)}
    {hH1 : ∀ c, H c 1 = f' (γ c)} {hK1 : ∀ c, K c 1 = g' (γ c)}
    {hH0' : ∀ c, H₁ c 0 = α₁ (f c)} {hK0' : ∀ c, K₁ c 0 = β₁ (g c)}
    {hH1' : ∀ c, H₁ c 1 = f' (γ₁ c)} {hK1' : ∀ c, K₁ c 1 = g' (γ₁ c)}
    (hα : ∀ a, α a = α₁ a) (hβ : ∀ b, β b = β₁ b) (hγ : ∀ c, γ c = γ₁ c)
    (hH : ∀ c t, H c t = H₁ c t) (hK : ∀ c t, K c t = K₁ c t) (x : DMC f g) :
    phi α β γ H K hH0 hK0 hH1 hK1 x = phi α₁ β₁ γ₁ H₁ K₁ hH0' hK0' hH1' hK1' x := by
  obtain rfl : α = α₁ := funext hα
  obtain rfl : β = β₁ := funext hβ
  obtain rfl : γ = γ₁ := funext hγ
  obtain rfl : H = H₁ := funext fun c ↦ funext (hH c)
  obtain rfl : K = K₁ := funext fun c ↦ funext (hK c)
  rfl

/-- Continuity of `phi`, jointly in a parameter `s ∈ I` on which the data depend
continuously. -/
private lemma continuous_phi_family (α : I → A → A') (β : I → B → B') (γ : I → C → C')
    (H : I → C → I → A') (K : I → C → I → B')
    (hH0 : ∀ s c, H s c 0 = α s (f c)) (hK0 : ∀ s c, K s c 0 = β s (g c))
    (hH1 : ∀ s c, H s c 1 = f' (γ s c)) (hK1 : ∀ s c, K s c 1 = g' (γ s c))
    (hα : Continuous fun p : I × A ↦ α p.1 p.2) (hβ : Continuous fun p : I × B ↦ β p.1 p.2)
    (hγ : Continuous fun p : I × C ↦ γ p.1 p.2)
    (hH : Continuous fun p : I × C × I ↦ H p.1 p.2.1 p.2.2)
    (hK : Continuous fun p : I × C × I ↦ K p.1 p.2.1 p.2.2) :
    Continuous fun p : I × DMC f g ↦
      phi (α p.1) (β p.1) (γ p.1) (H p.1) (K p.1) (hH0 p.1) (hK0 p.1) (hH1 p.1) (hK1 p.1) p.2 := by
  refine continuous_of_prod (continuous_inA.comp hα) (continuous_inB.comp hβ) ?_
  change Continuous fun p : I × (C × I) ↦ phiW (γ p.1) (H p.1) (K p.1) p.2.1 p.2.2
  have ht : Continuous fun p : I × (C × I) ↦ ((p.2.2 : I) : ℝ) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hc : Continuous fun p : I × (C × I) ↦ p.2.1 := continuous_fst.comp continuous_snd
  have hA' : Continuous fun p : I × (C × I) ↦ (inA (H p.1 p.2.1 (cl (3 * p.2.2))) : DMC f' g') :=
    continuous_inA.comp (hH.comp (continuous_fst.prodMk (hc.prodMk
      (continuous_cl.comp (continuous_const.mul ht)))))
  have hC' : Continuous fun p : I × (C × I) ↦
      (cyl (γ p.1 p.2.1) (cl (3 * p.2.2 - 1)) : DMC f' g') :=
    continuous_cyl.comp ((hγ.comp (continuous_fst.prodMk hc)).prodMk
      (continuous_cl.comp ((continuous_const.mul ht).sub continuous_const)))
  have hB' :
      Continuous fun p : I × (C × I) ↦ (inB (K p.1 p.2.1 (cl (3 - 3 * p.2.2))) : DMC f' g') :=
    continuous_inB.comp (hK.comp (continuous_fst.prodMk (hc.prodMk
      (continuous_cl.comp (continuous_const.sub (continuous_const.mul ht))))))
  refine Continuous.if_le hA' (Continuous.if_le hC' hB' ht continuous_const ?_) ht
    continuous_const ?_
  · intro p hp
    rw [hp]
    norm_num [cl_one, cl_zero, cyl_one, hK1]
  · intro p hp
    rw [hp]
    norm_num [cl_one, cl_zero, cyl_zero, hH1]

/-- `phi` as a bundled continuous map. -/
private def phiCM (α : A → A') (β : B → B') (γ : C → C') (H : C → I → A') (K : C → I → B')
    (hH0 : ∀ c, H c 0 = α (f c)) (hK0 : ∀ c, K c 0 = β (g c))
    (hH1 : ∀ c, H c 1 = f' (γ c)) (hK1 : ∀ c, K c 1 = g' (γ c))
    (hα : Continuous α) (hβ : Continuous β) (hγ : Continuous γ)
    (hH : Continuous fun p : C × I ↦ H p.1 p.2) (hK : Continuous fun p : C × I ↦ K p.1 p.2) :
    C(DMC f g, DMC f' g') :=
  ⟨phi α β γ H K hH0 hK0 hH1 hK1, by
    have := continuous_phi_family (f := f) (g := g) (fun _ ↦ α) (fun _ ↦ β) (fun _ ↦ γ)
      (fun _ ↦ H) (fun _ ↦ K) (fun _ ↦ hH0) (fun _ ↦ hK0) (fun _ ↦ hH1) (fun _ ↦ hK1)
      (hα.comp continuous_snd) (hβ.comp continuous_snd) (hγ.comp continuous_snd)
      (hH.comp continuous_snd) (hK.comp continuous_snd)
    exact this.comp (by fun_prop : Continuous fun x : DMC f g ↦ ((0 : I), x))⟩

@[local simp] private lemma phiCM_apply {α : A → A'} {β : B → B'} {γ : C → C'} {H : C → I → A'}
    {K : C → I → B'} {hH0 : ∀ c, H c 0 = α (f c)} {hK0 : ∀ c, K c 0 = β (g c)}
    {hH1 : ∀ c, H c 1 = f' (γ c)} {hK1 : ∀ c, K c 1 = g' (γ c)} {hα : Continuous α}
    {hβ : Continuous β} {hγ : Continuous γ} {hH : Continuous fun p : C × I ↦ H p.1 p.2}
    {hK : Continuous fun p : C × I ↦ K p.1 p.2} (x : DMC f g) :
    phiCM α β γ H K hH0 hK0 hH1 hK1 hα hβ hγ hH hK x = phi α β γ H K hH0 hK0 hH1 hK1 x := rfl

end Phi

attribute [local simp] phi_inA phi_inB phi_cyl phiCM_apply

section Reparam

/-- Reparametrization of the cylinder coordinate by `θ`. -/
private def reparam (θ : I → I) (h0 : θ 0 = 0) (h1 : θ 1 = 1) : DMC f g → DMC f g :=
  desc inA inB (fun c t ↦ cyl c (θ t)) (fun c ↦ by simp [h0, cyl_zero])
    (fun c ↦ by simp [h1, cyl_one])

@[local simp] private lemma reparam_cyl {θ : I → I} {h0 : θ 0 = 0} {h1 : θ 1 = 1} (c : C) (t : I) :
    reparam (f := f) (g := g) θ h0 h1 (cyl c t) = cyl c (θ t) := rfl

private def reparamCM (θ : I → I) (hθ : Continuous θ) (h0 : θ 0 = 0) (h1 : θ 1 = 1) :
    C(DMC f g, DMC f g) :=
  ⟨reparam θ h0 h1, continuous_desc continuous_inA continuous_inB
    (continuous_cyl.comp (continuous_fst.prodMk (hθ.comp continuous_snd)))⟩

@[local simp] private lemma reparamCM_inA {θ : I → I} {hθ : Continuous θ} {h0 : θ 0 = 0}
    {h1 : θ 1 = 1} (a : A) : reparamCM (f := f) (g := g) θ hθ h0 h1 (inA a) = inA a := rfl
@[local simp] private lemma reparamCM_inB {θ : I → I} {hθ : Continuous θ} {h0 : θ 0 = 0}
    {h1 : θ 1 = 1} (b : B) : reparamCM (f := f) (g := g) θ hθ h0 h1 (inB b) = inB b := rfl
@[local simp] private lemma reparamCM_cyl {θ : I → I} {hθ : Continuous θ} {h0 : θ 0 = 0}
    {h1 : θ 1 = 1} (c : C) (t : I) :
    reparamCM (f := f) (g := g) θ hθ h0 h1 (cyl c t) = cyl c (θ t) := rfl

/-- A reparametrization of the cylinder coordinate is homotopic to the identity. -/
private lemma reparamCM_homotopic (θ : I → I) (hθ : Continuous θ) (h0 : θ 0 = 0)
    (h1 : θ 1 = 1) : (reparamCM (f := f) (g := g) θ hθ h0 h1).Homotopic (ContinuousMap.id _) := by
  let θs : I → I → I := fun s t ↦ cl ((1 - (s : ℝ)) * (θ t : ℝ) + (s : ℝ) * (t : ℝ))
  have hs0 : ∀ s, θs s 0 = 0 := fun s ↦ by simp [θs, h0, cl_zero]
  have hs1 : ∀ s, θs s 1 = 1 := fun s ↦ by simp [θs, h1, cl_one]
  refine homotopic_of_continuous
    (fun p : I × DMC f g ↦ desc inA inB (fun c t ↦ cyl c (θs p.1 t))
      (fun c ↦ by simp [hs0, cyl_zero]) (fun c ↦ by simp [hs1, cyl_one]) p.2) ?_ ?_ ?_
  · refine continuous_of_prod ?_ ?_ ?_
    · exact continuous_inA.comp continuous_snd
    · exact continuous_inB.comp continuous_snd
    · change Continuous fun p : I × (C × I) ↦ (cyl p.2.1 (θs p.1 p.2.2) : DMC f g)
      have hc : Continuous fun p : I × (C × I) ↦ p.2.1 := continuous_fst.comp continuous_snd
      have hs : Continuous fun p : I × (C × I) ↦ ((p.1 : I) : ℝ) :=
        continuous_subtype_val.comp continuous_fst
      have ht : Continuous fun p : I × (C × I) ↦ ((p.2.2 : I) : ℝ) :=
        continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
      have hθ' : Continuous fun p : I × (C × I) ↦ ((θ p.2.2 : I) : ℝ) :=
        continuous_subtype_val.comp (hθ.comp (continuous_snd.comp continuous_snd))
      exact (continuous_cyl (f := f) (g := g)).comp (hc.prodMk (continuous_cl.comp
        (((continuous_const.sub hs).mul hθ').add (hs.mul ht))))
  · intro x
    induction x using ind with
    | hA a => rfl
    | hB b => rfl
    | hC c t => simp [θs, cl_coe]
  · intro x
    induction x using ind with
    | hA a => rfl
    | hB b => rfl
    | hC c t => simp [θs, cl_coe]

end Reparam

attribute [local simp] reparam_cyl reparamCM_inA reparamCM_inB reparamCM_cyl

section Comp

/-- Concatenation of two paths `p` and `q` with `p 1 = q 0`. -/
private def concat {X : Type*} (p q : I → X) (r : I) : X :=
  if (r : ℝ) ≤ 1 / 2 then p (cl (2 * r)) else q (cl (2 * r - 1))

private lemma concat_zero {X : Type*} (p q : I → X) : concat p q 0 = p 0 := by
  simp [concat, cl_zero]

private lemma concat_one {X : Type*} (p q : I → X) : concat p q 1 = q 1 := by
  norm_num [concat, cl_one]

private lemma continuous_concat {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p q : Y → I → X} (hp : Continuous fun z : Y × I ↦ p z.1 z.2)
    (hq : Continuous fun z : Y × I ↦ q z.1 z.2) (hpq : ∀ y, p y 1 = q y 0) :
    Continuous fun z : Y × I ↦ concat (p z.1) (q z.1) z.2 := by
  have hr : Continuous fun z : Y × I ↦ ((z.2 : I) : ℝ) := continuous_subtype_val.comp continuous_snd
  refine Continuous.if_le (hp.comp (continuous_fst.prodMk (continuous_cl.comp
    (continuous_const.mul hr)))) (hq.comp (continuous_fst.prodMk (continuous_cl.comp
    ((continuous_const.mul hr).sub continuous_const)))) hr continuous_const ?_
  intro z hz
  simp only [hz]
  norm_num [cl_one, cl_zero, hpq]

/-- The real reparametrization comparing a composite of two `phi`s with one `phi`. -/
private def thS (T : ℝ) : ℝ :=
  if T ≤ 1 / 3 then T / 2 else if T ≤ 4 / 9 then (9 * T - 2) / 6 else
    if T ≤ 5 / 9 then 3 * T - 1 else if T ≤ 2 / 3 then (9 * T - 1) / 6 else (1 + T) / 2

private lemma continuous_thS : Continuous thS := by
  refine Continuous.if_le (by fun_prop) (Continuous.if_le (by fun_prop)
    (Continuous.if_le (by fun_prop) (Continuous.if_le (by fun_prop) (by fun_prop) continuous_id
      continuous_const ?_) continuous_id continuous_const ?_) continuous_id continuous_const ?_)
    continuous_id continuous_const ?_
  all_goals
    intro x hx
    subst hx
    norm_num

private lemma thS_mem (T : ℝ) (h0 : 0 ≤ T) (h1 : T ≤ 1) : 0 ≤ thS T ∧ thS T ≤ 1 := by
  unfold thS
  split_ifs <;> constructor <;> linarith

private def thetaStar (t : I) : I := cl (thS t)

private lemma coe_thetaStar (t : I) : (thetaStar t : ℝ) = thS t :=
  coe_cl (thS_mem t t.2.1 t.2.2).1 (thS_mem t t.2.1 t.2.2).2

private lemma continuous_thetaStar : Continuous thetaStar :=
  continuous_cl.comp (continuous_thS.comp continuous_subtype_val)

private lemma thetaStar_zero : thetaStar 0 = 0 := by
  apply Subtype.ext; rw [coe_thetaStar]; norm_num [thS]

private lemma thetaStar_one : thetaStar 1 = 1 := by
  apply Subtype.ext; rw [coe_thetaStar]; norm_num [thS]

variable {A' B' C' A'' B'' C'' : Type*} [TopologicalSpace A'] [TopologicalSpace B']
  [TopologicalSpace C'] [TopologicalSpace A''] [TopologicalSpace B''] [TopologicalSpace C'']
  {f' : C' → A'} {g' : C' → B'} {f'' : C'' → A''} {g'' : C'' → B''}

/-- **Composition of `phi`s**: up to a reparametrization of the cylinder, the composite of two
maps of the form `phi` is the `phi` of the composite data, with concatenated homotopies. -/
private lemma phi_comp (α : A → A') (β : B → B') (γ : C → C') (H : C → I → A') (K : C → I → B')
    (hH0 : ∀ c, H c 0 = α (f c)) (hK0 : ∀ c, K c 0 = β (g c))
    (hH1 : ∀ c, H c 1 = f' (γ c)) (hK1 : ∀ c, K c 1 = g' (γ c))
    (α' : A' → A'') (β' : B' → B'') (γ' : C' → C'') (H' : C' → I → A'') (K' : C' → I → B'')
    (hH0' : ∀ c, H' c 0 = α' (f' c)) (hK0' : ∀ c, K' c 0 = β' (g' c))
    (hH1' : ∀ c, H' c 1 = f'' (γ' c)) (hK1' : ∀ c, K' c 1 = g'' (γ' c)) (x : DMC f g) :
    phi α' β' γ' H' K' hH0' hK0' hH1' hK1' (phi α β γ H K hH0 hK0 hH1 hK1 x) =
      phi (α' ∘ α) (β' ∘ β) (γ' ∘ γ) (fun c ↦ concat (fun r ↦ α' (H c r)) (H' (γ c)))
        (fun c ↦ concat (fun r ↦ β' (K c r)) (K' (γ c)))
        (fun c ↦ by simp [concat_zero, hH0]) (fun c ↦ by simp [concat_zero, hK0])
        (fun c ↦ by simp [concat_one, hH1']) (fun c ↦ by simp [concat_one, hK1'])
        (reparam thetaStar thetaStar_zero thetaStar_one x) := by
  induction x using ind with
  | hA a => rfl
  | hB b => rfl
  | hC c t =>
    rw [phi_cyl, reparam_cyl, phi_cyl]
    have ht0 := t.2.1
    have ht1 := t.2.2
    set T : ℝ := (t : ℝ) with hT
    have hθ := coe_thetaStar t
    rcases le_or_gt T (1 / 3) with h1 | h1
    · have hs : thS T = T / 2 := by rw [thS, if_pos h1]
      rw [phiW_of_le h1, phi_inA, phiW_of_le (by rw [hθ, hs]; linarith)]
      have hc : ((cl (3 * (thetaStar t : ℝ))) : ℝ) = 3 * T / 2 := by
        rw [hθ, hs, coe_cl (by linarith) (by linarith)]; ring
      simp only [concat, hc, show 3 * T / 2 ≤ 1 / 2 by linarith, if_true, Function.comp]
      congr 3
      exact congrArg cl (by rw [hT]; ring)
    rcases le_or_gt T (2 / 3) with h2 | h2
    · rw [phiW_of_mid h1 h2, phi_cyl]
      have hu0 : 0 ≤ 3 * T - 1 := by linarith
      have hu1 : 3 * T - 1 ≤ 1 := by linarith
      have hu : ((cl (3 * T - 1)) : ℝ) = 3 * T - 1 := coe_cl hu0 hu1
      rcases le_or_gt T (4 / 9) with h3 | h3
      · have hs : thS T = (9 * T - 2) / 6 := by rw [thS, if_neg (not_le.2 h1), if_pos h3]
        rw [phiW_of_le (by rw [hu]; linarith), phiW_of_le (by rw [hθ, hs]; linarith)]
        have hc : ((cl (3 * (thetaStar t : ℝ))) : ℝ) = (9 * T - 2) / 2 := by
          rw [hθ, hs, coe_cl (by linarith) (by linarith)]; ring
        simp only [concat, hc, show ¬ (9 * T - 2) / 2 ≤ 1 / 2 by linarith, if_false]
        congr 2
        exact congrArg cl (by rw [hu]; ring)
      rcases le_or_gt T (5 / 9) with h4 | h4
      · have hs : thS T = 3 * T - 1 := by
          rw [thS, if_neg (not_le.2 h1), if_neg (not_le.2 h3), if_pos h4]
        rw [phiW_of_mid (by rw [hu]; linarith) (by rw [hu]; linarith),
          phiW_of_mid (by rw [hθ, hs]; linarith) (by rw [hθ, hs]; linarith)]
        congr 1
        exact congrArg cl (by rw [hu, hθ, hs])
      · have hs : thS T = (9 * T - 1) / 6 := by
          rw [thS, if_neg (not_le.2 h1), if_neg (not_le.2 h3), if_neg (not_le.2 h4), if_pos h2]
        rw [phiW_of_gt (by rw [hu]; linarith), phiW_of_gt (by rw [hθ, hs]; linarith)]
        have hc : ((cl (3 - 3 * (thetaStar t : ℝ))) : ℝ) = (7 - 9 * T) / 2 := by
          rw [hθ, hs, coe_cl (by linarith) (by linarith)]; ring
        simp only [concat, hc]
        rcases eq_or_lt_of_le h2 with h5 | h5
        · have hT' : T = 2 / 3 := h5
          rw [if_pos (by rw [hT']; norm_num)]
          have e1 : cl (3 - 3 * ((cl (3 * T - 1)) : ℝ)) = 0 := by
            rw [hu, hT']; norm_num [cl_zero]
          have e2 : cl (2 * ((7 - 9 * T) / 2)) = 1 := by rw [hT']; norm_num [cl_one]
          rw [e1, e2, hK0', hK1]
        · rw [if_neg (by linarith)]
          congr 2
          exact congrArg cl (by rw [hu]; ring)
    · have hs : thS T = (1 + T) / 2 := by
        rw [thS, if_neg (by linarith), if_neg (by linarith), if_neg (by linarith),
          if_neg (by linarith)]
      rw [phiW_of_gt h2, phi_inB, phiW_of_gt (by rw [hθ, hs]; linarith)]
      have hc : ((cl (3 - 3 * (thetaStar t : ℝ))) : ℝ) = (3 - 3 * T) / 2 := by
        rw [hθ, hs, coe_cl (by linarith) (by linarith)]; ring
      simp only [concat, hc, show (3 - 3 * T) / 2 ≤ 1 / 2 by linarith, if_true, Function.comp]
      congr 3
      exact congrArg cl (by rw [hT]; ring)

end Comp

section Homotopies

variable {A' B' C' : Type*} [TopologicalSpace A'] [TopologicalSpace B'] [TopologicalSpace C']
  {f' : C' → A'} {g' : C' → B'}

/-- A continuous family of data gives a homotopy between the corresponding `phi`s. -/
private lemma homotopic_of_family {F₀ F₁ : C(DMC f g, DMC f' g')}
    (α : I → A → A') (β : I → B → B') (γ : I → C → C')
    (H : I → C → I → A') (K : I → C → I → B')
    (hH0 : ∀ s c, H s c 0 = α s (f c)) (hK0 : ∀ s c, K s c 0 = β s (g c))
    (hH1 : ∀ s c, H s c 1 = f' (γ s c)) (hK1 : ∀ s c, K s c 1 = g' (γ s c))
    (hα : Continuous fun p : I × A ↦ α p.1 p.2) (hβ : Continuous fun p : I × B ↦ β p.1 p.2)
    (hγ : Continuous fun p : I × C ↦ γ p.1 p.2)
    (hH : Continuous fun p : I × C × I ↦ H p.1 p.2.1 p.2.2)
    (hK : Continuous fun p : I × C × I ↦ K p.1 p.2.1 p.2.2)
    (h0 : ∀ x, F₀ x = phi (α 0) (β 0) (γ 0) (H 0) (K 0) (hH0 0) (hK0 0) (hH1 0) (hK1 0) x)
    (h1 : ∀ x, F₁ x = phi (α 1) (β 1) (γ 1) (H 1) (K 1) (hH0 1) (hK0 1) (hH1 1) (hK1 1) x) :
    F₀.Homotopic F₁ :=
  homotopic_of_continuous _ (continuous_phi_family α β γ H K hH0 hK0 hH1 hK1 hα hβ hγ hH hK)
    (fun x ↦ (h0 x).symm) (fun x ↦ (h1 x).symm)

variable {A'' B'' C'' : Type*} [TopologicalSpace A''] [TopologicalSpace B'']
  [TopologicalSpace C''] {f'' : C'' → A''} {g'' : C'' → B''}

/-- A composite of two `phi`s is homotopic to the `phi` of the composite data. -/
private lemma comp_homotopic {F : C(DMC f g, DMC f' g')} {F' : C(DMC f' g', DMC f'' g'')}
    {G : C(DMC f g, DMC f'' g'')}
    (α : A → A') (β : B → B') (γ : C → C') (H : C → I → A') (K : C → I → B')
    (hH0 : ∀ c, H c 0 = α (f c)) (hK0 : ∀ c, K c 0 = β (g c))
    (hH1 : ∀ c, H c 1 = f' (γ c)) (hK1 : ∀ c, K c 1 = g' (γ c))
    (α' : A' → A'') (β' : B' → B'') (γ' : C' → C'') (H' : C' → I → A'') (K' : C' → I → B'')
    (hH0' : ∀ c, H' c 0 = α' (f' c)) (hK0' : ∀ c, K' c 0 = β' (g' c))
    (hH1' : ∀ c, H' c 1 = f'' (γ' c)) (hK1' : ∀ c, K' c 1 = g'' (γ' c))
    (hF : ∀ x, F x = phi α β γ H K hH0 hK0 hH1 hK1 x)
    (hF' : ∀ x, F' x = phi α' β' γ' H' K' hH0' hK0' hH1' hK1' x)
    (hG : ∀ x, G x = phi (α' ∘ α) (β' ∘ β) (γ' ∘ γ)
      (fun c ↦ concat (fun r ↦ α' (H c r)) (H' (γ c)))
      (fun c ↦ concat (fun r ↦ β' (K c r)) (K' (γ c)))
      (fun c ↦ by simp [concat_zero, hH0]) (fun c ↦ by simp [concat_zero, hK0])
      (fun c ↦ by simp [concat_one, hH1']) (fun c ↦ by simp [concat_one, hK1']) x) :
    (F'.comp F).Homotopic G := by
  have : F'.comp F = G.comp (reparamCM thetaStar continuous_thetaStar thetaStar_zero
      thetaStar_one) := by
    ext x
    simp only [ContinuousMap.comp_apply, hF, hF', hG]
    exact phi_comp α β γ H K hH0 hK0 hH1 hK1 α' β' γ' H' K' hH0' hK0' hH1' hK1' x
  rw [this]
  simpa using (ContinuousMap.Homotopic.refl G).comp (reparamCM_homotopic _ _ _ _)

end Homotopies

section Invariance

/-- A map with a left and a right homotopy inverse is a homotopy equivalence. -/
private lemma nonempty_homotopyEquiv_of_left_right {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (F : C(X, Y)) (G G' : C(Y, X))
    (hl : (G.comp F).Homotopic (ContinuousMap.id X))
    (hr : (F.comp G').Homotopic (ContinuousMap.id Y)) :
    Nonempty (ContinuousMap.HomotopyEquiv X Y) := by
  have h1 : (G.comp (F.comp G')).Homotopic G := by
    simpa using (ContinuousMap.Homotopic.refl G).comp hr
  have h2 : ((G.comp F).comp G').Homotopic G' := by
    simpa using hl.comp (ContinuousMap.Homotopic.refl G')
  have hG : G.Homotopic G' := h1.symm.trans (by rwa [ContinuousMap.comp_assoc] at h2)
  exact ⟨⟨F, G, hl, ((ContinuousMap.Homotopic.refl F).comp hG).trans hr⟩⟩

private def thirdθ (t : I) : I := cl (3 * t - 1)

private lemma continuous_thirdθ : Continuous thirdθ :=
  continuous_cl.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)

private lemma thirdθ_zero : thirdθ 0 = 0 := cl_of_le (by simp)
private lemma thirdθ_one : thirdθ 1 = 1 := cl_of_ge (by norm_num)

/-- The reparametrization collapsing the outer thirds of the cylinder. -/
private def thirdCM : C(DMC f g, DMC f g) :=
  reparamCM thirdθ continuous_thirdθ thirdθ_zero thirdθ_one

private lemma thirdCM_homotopic : (thirdCM (f := f) (g := g)).Homotopic (ContinuousMap.id _) :=
  reparamCM_homotopic _ _ _ _

private lemma phi_const_eq (x : DMC f g) :
    phi id id id (fun c _ ↦ f c) (fun c _ ↦ g c) (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl) x = thirdCM x := by
  induction x using ind with
  | hA a => rfl
  | hB b => rfl
  | hC c t =>
    rw [phi_cyl]
    change _ = cyl c (thirdθ t)
    rcases le_or_gt (t : ℝ) (1 / 3) with h | h
    · rw [phiW_of_le h, show thirdθ t = 0 from cl_of_le (by linarith), cyl_zero]
    rcases le_or_gt (t : ℝ) (2 / 3) with h' | h'
    · rw [phiW_of_mid h h']; rfl
    · rw [phiW_of_gt h', show thirdθ t = 1 from cl_of_ge (by linarith), cyl_one]

private lemma min_min_eq (r : I) :
    min (min (2 * (r : ℝ)) (2 - 2 * r)) 1 =
      (if (r : ℝ) ≤ 1 / 2 then 2 * (r : ℝ) else 2 - 2 * (r : ℝ) : ℝ) := by
  have := r.2.1; have := r.2.2
  split_ifs with h
  · rw [min_eq_left (show 2 * (r : ℝ) ≤ 2 - 2 * r by linarith),
      min_eq_left (show 2 * (r : ℝ) ≤ 1 by linarith)]
  · rw [min_eq_right (show 2 - 2 * (r : ℝ) ≤ 2 * r by linarith),
      min_eq_left (show 2 - 2 * (r : ℝ) ≤ 1 by linarith)]

private lemma min_min_zero (r : I) : min (min (2 * (r : ℝ)) (2 - 2 * r)) 0 = 0 :=
  min_eq_right (le_min (by linarith [r.2.1, r.2.2]) (by linarith [r.2.1, r.2.2]))

variable {f₀ f₁ : C → A} {g₀ g₁ : C → B}

/-- Following a homotopy and then its reverse is homotopic to the identity. -/
private lemma rev_comp_homotopic (H : C → I → A) (K : C → I → B)
    (hHc : Continuous fun p : C × I ↦ H p.1 p.2) (hKc : Continuous fun p : C × I ↦ K p.1 p.2)
    (hH0 : ∀ c, H c 0 = f₀ c) (hH1 : ∀ c, H c 1 = f₁ c)
    (hK0 : ∀ c, K c 0 = g₀ c) (hK1 : ∀ c, K c 1 = g₁ c)
    (E : C(DMC f₀ g₀, DMC f₁ g₁)) (E' : C(DMC f₁ g₁, DMC f₀ g₀))
    (hE : ∀ x, E x = phi id id id H K hH0 hK0 hH1 hK1 x)
    (hE' : ∀ x, E' x = phi id id id (fun c r ↦ H c (symm r)) (fun c r ↦ K c (symm r))
      (fun c ↦ by simp [hH1]) (fun c ↦ by simp [hK1]) (fun c ↦ by simp [hH0])
      (fun c ↦ by simp [hK0]) x) :
    (E'.comp E).Homotopic (ContinuousMap.id _) := by
  have hsymm : Continuous fun p : C × I ↦ (p.1, symm p.2) :=
    continuous_fst.prodMk (continuous_symm.comp continuous_snd)
  let Hs : I → C → I → A := fun s c r ↦ H c (cl (min (min (2 * (r : ℝ)) (2 - 2 * r)) (1 - s)))
  let Ks : I → C → I → B := fun s c r ↦ K c (cl (min (min (2 * (r : ℝ)) (2 - 2 * r)) (1 - s)))
  have hr : ∀ s : I, min (min (2 * ((0 : I) : ℝ)) (2 - 2 * ((0 : I) : ℝ))) (1 - (s : ℝ)) = 0 :=
    fun s ↦ by simp; linarith [s.2.2]
  have hr' : ∀ s : I, min (min (2 * ((1 : I) : ℝ)) (2 - 2 * ((1 : I) : ℝ))) (1 - (s : ℝ)) = 0 :=
    fun s ↦ by norm_num; linarith [s.2.2]
  have hHs0 : ∀ s c, Hs s c 0 = id (f₀ c) := fun s c ↦ by simp only [Hs, hr, cl_zero, hH0, id_eq]
  have hHs1 : ∀ s c, Hs s c 1 = f₀ (id c) := fun s c ↦ by simp only [Hs, hr', cl_zero, hH0, id_eq]
  have hKs0 : ∀ s c, Ks s c 0 = id (g₀ c) := fun s c ↦ by simp only [Ks, hr, cl_zero, hK0, id_eq]
  have hKs1 : ∀ s c, Ks s c 1 = g₀ (id c) := fun s c ↦ by simp only [Ks, hr', cl_zero, hK0, id_eq]
  have hm : Continuous fun p : I × C × I ↦
      cl (min (min (2 * ((p.2.2 : I) : ℝ)) (2 - 2 * (p.2.2 : ℝ))) (1 - (p.1 : ℝ))) := by
    refine continuous_cl.comp ?_
    have ht : Continuous fun p : I × C × I ↦ ((p.2.2 : I) : ℝ) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact ((continuous_const.mul ht).min (continuous_const.sub (continuous_const.mul ht))).min
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
  have hcat : Continuous fun p : C × I ↦
      concat (fun r ↦ id (H p.1 r)) (fun r ↦ H (id p.1) (symm r)) p.2 :=
    continuous_concat (p := fun c r ↦ id (H c r)) (q := fun c r ↦ H (id c) (symm r)) hHc
      (hHc.comp hsymm) (fun c ↦ by simp)
  have hcatK : Continuous fun p : C × I ↦
      concat (fun r ↦ id (K p.1 r)) (fun r ↦ K (id p.1) (symm r)) p.2 :=
    continuous_concat (p := fun c r ↦ id (K c r)) (q := fun c r ↦ K (id c) (symm r)) hKc
      (hKc.comp hsymm) (fun c ↦ by simp)
  let G : C(DMC f₀ g₀, DMC f₀ g₀) := phiCM (id ∘ id) (id ∘ id) (id ∘ id)
    (fun c ↦ concat (fun r ↦ id (H c r)) (fun r ↦ H (id c) (symm r)))
    (fun c ↦ concat (fun r ↦ id (K c r)) (fun r ↦ K (id c) (symm r)))
    (fun c ↦ by simp [concat_zero, hH0]) (fun c ↦ by simp [concat_zero, hK0])
    (fun c ↦ by simp [concat_one, hH0]) (fun c ↦ by simp [concat_one, hK0])
    continuous_id continuous_id continuous_id hcat hcatK
  refine (comp_homotopic (G := G) id id id H K hH0 hK0 hH1 hK1 id id id
    (fun c r ↦ H c (symm r)) (fun c r ↦ K c (symm r)) _ _ _ _ hE hE' (fun _ ↦ rfl)).trans ?_
  refine (homotopic_of_family (F₁ := thirdCM) (fun _ ↦ id) (fun _ ↦ id) (fun _ ↦ id) Hs Ks
    hHs0 hKs0 hHs1 hKs1 (continuous_snd) (continuous_snd) (continuous_snd)
    (hHc.comp ((continuous_fst.comp continuous_snd).prodMk hm))
    (hKc.comp ((continuous_fst.comp continuous_snd).prodMk hm)) ?_ ?_).trans thirdCM_homotopic
  · intro x
    simp only [G, phiCM_apply]
    refine phi_congr (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun c r ↦ ?_) (fun c r ↦ ?_) x
    · simp only [concat, Hs, Set.Icc.coe_zero, sub_zero, min_min_eq, id]
      split_ifs with h
      · rfl
      · congr 1
        apply Subtype.ext
        have := r.2.2
        rw [not_le] at h
        rw [coe_symm_eq, coe_cl (by linarith) (by linarith), coe_cl (by linarith) (by linarith)]
        ring
    · simp only [concat, Ks, Set.Icc.coe_zero, sub_zero, min_min_eq, id]
      split_ifs with h
      · rfl
      · congr 1
        apply Subtype.ext
        have := r.2.2
        rw [not_le] at h
        rw [coe_symm_eq, coe_cl (by linarith) (by linarith), coe_cl (by linarith) (by linarith)]
        ring
  · intro x
    rw [← phi_const_eq]
    refine phi_congr (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun c r ↦ ?_) (fun c r ↦ ?_) x
    · simp only [Hs, Set.Icc.coe_one, sub_self, min_min_zero, cl_zero, hH0]
    · simp only [Ks, Set.Icc.coe_one, sub_self, min_min_zero, cl_zero, hK0]

/-- Composite data of two `phi`s, bundled. -/
private def compCM {A' B' C' A'' B'' C'' : Type*} [TopologicalSpace A'] [TopologicalSpace B']
    [TopologicalSpace C'] [TopologicalSpace A''] [TopologicalSpace B''] [TopologicalSpace C'']
    {f' : C' → A'} {g' : C' → B'} {f'' : C'' → A''} {g'' : C'' → B''}
    (α : A → A') (β : B → B') (γ : C → C') (H : C → I → A') (K : C → I → B')
    (hH0 : ∀ c, H c 0 = α (f c)) (hK0 : ∀ c, K c 0 = β (g c))
    (hH1 : ∀ c, H c 1 = f' (γ c)) (hK1 : ∀ c, K c 1 = g' (γ c))
    (α' : A' → A'') (β' : B' → B'') (γ' : C' → C'') (H' : C' → I → A'') (K' : C' → I → B'')
    (hH0' : ∀ c, H' c 0 = α' (f' c)) (hK0' : ∀ c, K' c 0 = β' (g' c))
    (hH1' : ∀ c, H' c 1 = f'' (γ' c)) (hK1' : ∀ c, K' c 1 = g'' (γ' c))
    (hα : Continuous α) (hβ : Continuous β) (hγ : Continuous γ)
    (hH : Continuous fun p : C × I ↦ H p.1 p.2) (hK : Continuous fun p : C × I ↦ K p.1 p.2)
    (hα' : Continuous α') (hβ' : Continuous β') (hγ' : Continuous γ')
    (hH' : Continuous fun p : C' × I ↦ H' p.1 p.2) (hK' : Continuous fun p : C' × I ↦ K' p.1 p.2) :
    C(DMC f g, DMC f'' g'') :=
  phiCM (α' ∘ α) (β' ∘ β) (γ' ∘ γ) (fun c ↦ concat (fun r ↦ α' (H c r)) (H' (γ c)))
    (fun c ↦ concat (fun r ↦ β' (K c r)) (K' (γ c)))
    (fun c ↦ by simp [concat_zero, hH0]) (fun c ↦ by simp [concat_zero, hK0])
    (fun c ↦ by simp [concat_one, hH1']) (fun c ↦ by simp [concat_one, hK1'])
    (hα'.comp hα) (hβ'.comp hβ) (hγ'.comp hγ)
    (continuous_concat (p := fun c r ↦ α' (H c r)) (q := fun c r ↦ H' (γ c) r)
      (hα'.comp hH) (hH'.comp ((hγ.comp continuous_fst).prodMk continuous_snd))
      (fun c ↦ by simp [hH1, hH0']))
    (continuous_concat (p := fun c r ↦ β' (K c r)) (q := fun c r ↦ K' (γ c) r)
      (hβ'.comp hK) (hK'.comp ((hγ.comp continuous_fst).prodMk continuous_snd))
      (fun c ↦ by simp [hK1, hK0']))

/-- **Homotopic attaching maps**: homotopies `f₀ ≃ f₁`, `g₀ ≃ g₁` give a homotopy equivalence
`D(f₀, g₀) ≃ D(f₁, g₁)`. -/
private lemma nonempty_homotopyEquiv_of_homotopy {f₀ f₁ : C → A} {g₀ g₁ : C → B}
    (H : C → I → A) (K : C → I → B)
    (hHc : Continuous fun p : C × I ↦ H p.1 p.2) (hKc : Continuous fun p : C × I ↦ K p.1 p.2)
    (hH0 : ∀ c, H c 0 = f₀ c) (hH1 : ∀ c, H c 1 = f₁ c)
    (hK0 : ∀ c, K c 0 = g₀ c) (hK1 : ∀ c, K c 1 = g₁ c) :
    Nonempty (ContinuousMap.HomotopyEquiv (DMC f₀ g₀) (DMC f₁ g₁)) := by
  have hsymm : Continuous fun p : C × I ↦ (p.1, symm p.2) :=
    continuous_fst.prodMk (continuous_symm.comp continuous_snd)
  let E : C(DMC f₀ g₀, DMC f₁ g₁) := phiCM id id id H K hH0 hK0 hH1 hK1
    continuous_id continuous_id continuous_id hHc hKc
  let E' : C(DMC f₁ g₁, DMC f₀ g₀) := phiCM id id id (fun c r ↦ H c (symm r))
    (fun c r ↦ K c (symm r)) (fun c ↦ by simp [hH1]) (fun c ↦ by simp [hK1])
    (fun c ↦ by simp [hH0]) (fun c ↦ by simp [hK0])
    continuous_id continuous_id continuous_id (hHc.comp hsymm) (hKc.comp hsymm)
  refine nonempty_homotopyEquiv_of_left_right E E' E'
    (rev_comp_homotopic H K hHc hKc hH0 hH1 hK0 hK1 E E' (fun _ ↦ rfl) (fun _ ↦ rfl)) ?_
  refine rev_comp_homotopic (fun c r ↦ H c (symm r)) (fun c r ↦ K c (symm r))
    (hHc.comp hsymm) (hKc.comp hsymm) (fun c ↦ by simp [hH1]) (fun c ↦ by simp [hH0])
    (fun c ↦ by simp [hK1]) (fun c ↦ by simp [hK0]) E' E (fun _ ↦ rfl) (fun x ↦ ?_)
  simp only [E, phiCM_apply]
  exact phi_congr (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun c r ↦ by simp)
    (fun c r ↦ by simp) x

variable {A' B' : Type*} [TopologicalSpace A'] [TopologicalSpace B']

/-- One half of the replacement of the ends: `Ψ ∘ Γ ≃ id`. -/
private lemma ends_left_inv (α : A → A') (α' : A' → A) (β : B → B') (β' : B' → B)
    (hα : Continuous α) (hα' : Continuous α') (hβ : Continuous β) (hβ' : Continuous β')
    (P : I × A → A) (R : I × B → B) (hP : Continuous P) (hR : Continuous R)
    (hP0 : ∀ a, P (0, a) = α' (α a)) (hP1 : ∀ a, P (1, a) = a)
    (hR0 : ∀ b, R (0, b) = β' (β b)) (hR1 : ∀ b, R (1, b) = b)
    (hf : Continuous f) (hg : Continuous g)
    (Γ : C(DMC f g, DMC (α ∘ f) (β ∘ g))) (Ψ : C(DMC (α ∘ f) (β ∘ g), DMC f g))
    (hΓ : ∀ x, Γ x = phi α β id (fun c _ ↦ α (f c)) (fun c _ ↦ β (g c)) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) x)
    (hΨ : ∀ x, Ψ x = phi α' β' id (fun c r ↦ P (r, f c)) (fun c r ↦ R (r, g c))
      (fun c ↦ hP0 (f c)) (fun c ↦ hR0 (g c)) (fun c ↦ hP1 (f c)) (fun c ↦ hR1 (g c)) x) :
    (Ψ.comp Γ).Homotopic (ContinuousMap.id _) := by
  have hPc : Continuous fun p : C × I ↦ P (p.2, f p.1) :=
    hP.comp (continuous_snd.prodMk (hf.comp continuous_fst))
  have hRc : Continuous fun p : C × I ↦ R (p.2, g p.1) :=
    hR.comp (continuous_snd.prodMk (hg.comp continuous_fst))
  refine (comp_homotopic (F := Γ) (F' := Ψ) (G := compCM (f' := α ∘ f) (g' := β ∘ g)
      (f'' := f) (g'' := g) α β id (fun c _ ↦ α (f c)) (fun c _ ↦ β (g c)) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) α' β' id (fun c r ↦ P (r, f c))
      (fun c r ↦ R (r, g c)) (fun c ↦ hP0 (f c)) (fun c ↦ hR0 (g c)) (fun c ↦ hP1 (f c))
      (fun c ↦ hR1 (g c)) hα hβ continuous_id ((hα.comp hf).comp continuous_fst)
      ((hβ.comp hg).comp continuous_fst) hα' hβ' continuous_id hPc hRc)
    α β id (fun c _ ↦ α (f c)) (fun c _ ↦ β (g c)) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) α' β' id (fun c r ↦ P (r, f c)) (fun c r ↦ R (r, g c)) (fun c ↦ hP0 (f c))
    (fun c ↦ hR0 (g c)) (fun c ↦ hP1 (f c)) (fun c ↦ hR1 (g c)) hΓ hΨ (fun _ ↦ rfl)).trans ?_
  let τ : I → I → I := fun s r ↦ cl (s + (1 - s) * max 0 (2 * (r : ℝ) - 1))
  have hτ0 : ∀ s, τ s 0 = s := fun s ↦ by
    simp only [τ, Set.Icc.coe_zero, mul_zero, zero_sub]
    rw [max_eq_left (by norm_num), mul_zero, add_zero, cl_coe]
  have hτ1 : ∀ s, τ s 1 = 1 := fun s ↦ by
    simp only [τ, Set.Icc.coe_one]
    rw [max_eq_right (by norm_num)]
    norm_num [cl_one]
  have hτc : Continuous fun p : I × C × I ↦ τ p.1 p.2.2 := by
    have hs : Continuous fun p : I × C × I ↦ ((p.1 : I) : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have ht : Continuous fun p : I × C × I ↦ ((p.2.2 : I) : ℝ) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact continuous_cl.comp (hs.add ((continuous_const.sub hs).mul
      (continuous_const.max ((continuous_const.mul ht).sub continuous_const))))
  have e0 : ∀ (s : I) (c : C), P (τ s 0, f c) = P (s, f c) := fun s c ↦ by rw [hτ0]
  have e0' : ∀ (s : I) (c : C), R (τ s 0, g c) = R (s, g c) := fun s c ↦ by rw [hτ0]
  have e1 : ∀ (s : I) (c : C), P (τ s 1, f c) = f (id c) := fun s c ↦ by rw [hτ1, hP1]; rfl
  have e1' : ∀ (s : I) (c : C), R (τ s 1, g c) = g (id c) := fun s c ↦ by rw [hτ1, hR1]; rfl
  refine (homotopic_of_family (F₁ := thirdCM) (fun s a ↦ P (s, a)) (fun s b ↦ R (s, b))
    (fun _ ↦ id) (fun s c r ↦ P (τ s r, f c)) (fun s c r ↦ R (τ s r, g c))
    e0 e0' e1 e1' hP hR continuous_snd
    (hP.comp (hτc.prodMk (hf.comp (continuous_fst.comp continuous_snd))))
    (hR.comp (hτc.prodMk (hg.comp (continuous_fst.comp continuous_snd)))) ?_ ?_).trans
    thirdCM_homotopic
  · intro x
    simp only [compCM, phiCM_apply]
    refine phi_congr (fun a ↦ (hP0 a).symm) (fun b ↦ (hR0 b).symm) (fun _ ↦ rfl)
      (fun c r ↦ ?_) (fun c r ↦ ?_) x
    · simp only [concat, τ, Set.Icc.coe_zero, zero_add, sub_zero, one_mul, id]
      split_ifs with h
      · rw [max_eq_left (by linarith), cl_zero, hP0]
      · rw [max_eq_right (by linarith)]
    · simp only [concat, τ, Set.Icc.coe_zero, zero_add, sub_zero, one_mul, id]
      split_ifs with h
      · rw [max_eq_left (by linarith), cl_zero, hR0]
      · rw [max_eq_right (by linarith)]
  · intro x
    rw [← phi_const_eq]
    refine phi_congr (fun a ↦ (hP1 a).symm) (fun b ↦ (hR1 b).symm) (fun _ ↦ rfl)
      (fun c r ↦ ?_) (fun c r ↦ ?_) x
    · simp only [τ, Set.Icc.coe_one, sub_self, zero_mul, add_zero, cl_one, hP1]
    · simp only [τ, Set.Icc.coe_one, sub_self, zero_mul, add_zero, cl_one, hR1]

/-- The comparison `E ∘ Γ' ≃ Ψ` in the replacement of the ends. -/
private lemma ends_comparison (α : A → A') (α' : A' → A) (β : B → B') (β' : B' → B)
    (hα : Continuous α) (hβ : Continuous β) (hα' : Continuous α') (hβ' : Continuous β')
    (P : I × A → A) (R : I × B → B) (hP : Continuous P) (hR : Continuous R)
    (hP0 : ∀ a, P (0, a) = α' (α a)) (hP1 : ∀ a, P (1, a) = a)
    (hR0 : ∀ b, R (0, b) = β' (β b)) (hR1 : ∀ b, R (1, b) = b)
    (hf : Continuous f) (hg : Continuous g)
    (Γ' : C(DMC (α ∘ f) (β ∘ g), DMC (α' ∘ (α ∘ f)) (β' ∘ (β ∘ g))))
    (E : C(DMC (α' ∘ (α ∘ f)) (β' ∘ (β ∘ g)), DMC f g)) (Ψ : C(DMC (α ∘ f) (β ∘ g), DMC f g))
    (hΓ' : ∀ x, Γ' x = phi α' β' id (fun c _ ↦ α' (α (f c))) (fun c _ ↦ β' (β (g c)))
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) x)
    (hE : ∀ x, E x = phi id id id (fun c r ↦ P (r, f c)) (fun c r ↦ R (r, g c))
      (fun c ↦ hP0 (f c)) (fun c ↦ hR0 (g c)) (fun c ↦ hP1 (f c)) (fun c ↦ hR1 (g c)) x)
    (hΨ : ∀ x, Ψ x = phi α' β' id (fun c r ↦ P (r, f c)) (fun c r ↦ R (r, g c))
      (fun c ↦ hP0 (f c)) (fun c ↦ hR0 (g c)) (fun c ↦ hP1 (f c)) (fun c ↦ hR1 (g c)) x) :
    (E.comp Γ').Homotopic Ψ := by
  have hPc : Continuous fun p : C × I ↦ P (p.2, f p.1) :=
    hP.comp (continuous_snd.prodMk (hf.comp continuous_fst))
  have hRc : Continuous fun p : C × I ↦ R (p.2, g p.1) :=
    hR.comp (continuous_snd.prodMk (hg.comp continuous_fst))
  refine (comp_homotopic (F := Γ') (F' := E) (G := compCM (f' := α' ∘ (α ∘ f))
      (g' := β' ∘ (β ∘ g)) (f'' := f) (g'' := g) α' β' id (fun c _ ↦ α' (α (f c)))
      (fun c _ ↦ β' (β (g c))) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
      id id id (fun c r ↦ P (r, f c)) (fun c r ↦ R (r, g c)) (fun c ↦ hP0 (f c))
      (fun c ↦ hR0 (g c)) (fun c ↦ hP1 (f c)) (fun c ↦ hR1 (g c)) hα' hβ' continuous_id
      ((hα'.comp (hα.comp hf)).comp continuous_fst) ((hβ'.comp (hβ.comp hg)).comp continuous_fst)
      continuous_id continuous_id continuous_id hPc hRc)
    α' β' id (fun c _ ↦ α' (α (f c))) (fun c _ ↦ β' (β (g c))) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ ↦ rfl) id id id (fun c r ↦ P (r, f c)) (fun c r ↦ R (r, g c))
    (fun c ↦ hP0 (f c)) (fun c ↦ hR0 (g c)) (fun c ↦ hP1 (f c)) (fun c ↦ hR1 (g c))
    hΓ' hE (fun _ ↦ rfl)).trans ?_
  let τ : I → I → I := fun s r ↦ cl ((1 - s) * max 0 (2 * (r : ℝ) - 1) + s * r)
  have hτ0 : ∀ s, τ s 0 = 0 := fun s ↦ by
    simp only [τ, Set.Icc.coe_zero, mul_zero, zero_sub, add_zero]
    rw [max_eq_left (by norm_num), mul_zero, cl_zero]
  have hτ1 : ∀ s, τ s 1 = 1 := fun s ↦ by
    simp only [τ, Set.Icc.coe_one]
    rw [max_eq_right (by norm_num)]
    norm_num [cl_one]
  have hτc : Continuous fun p : I × C × I ↦ τ p.1 p.2.2 := by
    have hs : Continuous fun p : I × C × I ↦ ((p.1 : I) : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have ht : Continuous fun p : I × C × I ↦ ((p.2.2 : I) : ℝ) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact continuous_cl.comp (((continuous_const.sub hs).mul
      (continuous_const.max ((continuous_const.mul ht).sub continuous_const))).add (hs.mul ht))
  have e0 : ∀ (s : I) (c : C), P (τ s 0, f c) = α' ((α ∘ f) c) := fun s c ↦ by
    rw [hτ0, hP0]; rfl
  have e0' : ∀ (s : I) (c : C), R (τ s 0, g c) = β' ((β ∘ g) c) := fun s c ↦ by
    rw [hτ0, hR0]; rfl
  have e1 : ∀ (s : I) (c : C), P (τ s 1, f c) = f (id c) := fun s c ↦ by rw [hτ1, hP1]; rfl
  have e1' : ∀ (s : I) (c : C), R (τ s 1, g c) = g (id c) := fun s c ↦ by rw [hτ1, hR1]; rfl
  refine homotopic_of_family (fun _ ↦ α') (fun _ ↦ β') (fun _ ↦ id)
    (fun s c r ↦ P (τ s r, f c)) (fun s c r ↦ R (τ s r, g c))
    e0 e0' e1 e1' (hα'.comp continuous_snd) (hβ'.comp continuous_snd) continuous_snd
    (hP.comp (hτc.prodMk (hf.comp (continuous_fst.comp continuous_snd))))
    (hR.comp (hτc.prodMk (hg.comp (continuous_fst.comp continuous_snd)))) ?_ ?_
  · intro x
    simp only [compCM, phiCM_apply]
    refine phi_congr (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun c r ↦ ?_) (fun c r ↦ ?_) x
    · simp only [concat, τ, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero, id]
      split_ifs with h
      · rw [max_eq_left (by linarith), cl_zero, hP0]
      · rw [max_eq_right (by linarith)]
    · simp only [concat, τ, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero, id]
      split_ifs with h
      · rw [max_eq_left (by linarith), cl_zero, hR0]
      · rw [max_eq_right (by linarith)]
  · intro x
    rw [hΨ]
    refine phi_congr (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun c r ↦ ?_) (fun c r ↦ ?_) x
    · simp only [τ, Set.Icc.coe_one, sub_self, zero_mul, zero_add, one_mul, cl_coe]
    · simp only [τ, Set.Icc.coe_one, sub_self, zero_mul, zero_add, one_mul, cl_coe]

/-- **Replacing the ends**: homotopy equivalences `A ≃ A'`, `B ≃ B'` give a homotopy equivalence
`D(α ∘ f, β ∘ g) ≃ D(f, g)`. -/
private lemma nonempty_homotopyEquiv_ends (eA : ContinuousMap.HomotopyEquiv A A')
    (eB : ContinuousMap.HomotopyEquiv B B') (hf : Continuous f) (hg : Continuous g) :
    Nonempty (ContinuousMap.HomotopyEquiv (DMC (eA.toFun ∘ f) (eB.toFun ∘ g)) (DMC f g)) := by
  set α := eA.toFun
  set α' := eA.invFun
  set β := eB.toFun
  set β' := eB.invFun
  obtain ⟨P⟩ := eA.left_inv
  obtain ⟨P'⟩ := eA.right_inv
  obtain ⟨R⟩ := eB.left_inv
  obtain ⟨R'⟩ := eB.right_inv
  have hP0 : ∀ a, P (0, a) = α' (α a) := fun a ↦ P.apply_zero a
  have hP1 : ∀ a, P (1, a) = a := fun a ↦ P.apply_one a
  have hR0 : ∀ b, R (0, b) = β' (β b) := fun b ↦ R.apply_zero b
  have hR1 : ∀ b, R (1, b) = b := fun b ↦ R.apply_one b
  have hP0' : ∀ a, P' (0, a) = α (α' a) := fun a ↦ P'.apply_zero a
  have hP1' : ∀ a, P' (1, a) = a := fun a ↦ P'.apply_one a
  have hR0' : ∀ b, R' (0, b) = β (β' b) := fun b ↦ R'.apply_zero b
  have hR1' : ∀ b, R' (1, b) = b := fun b ↦ R'.apply_one b
  have hαf : Continuous (α ∘ f) := α.continuous.comp hf
  have hβg : Continuous (β ∘ g) := β.continuous.comp hg
  let Γ : C(DMC f g, DMC (α ∘ f) (β ∘ g)) := phiCM α β id (fun c _ ↦ α (f c))
    (fun c _ ↦ β (g c)) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    α.continuous β.continuous continuous_id (hαf.comp continuous_fst) (hβg.comp continuous_fst)
  let Ψ : C(DMC (α ∘ f) (β ∘ g), DMC f g) := phiCM α' β' id (fun c r ↦ P (r, f c))
    (fun c r ↦ R (r, g c)) (fun c ↦ hP0 (f c)) (fun c ↦ hR0 (g c)) (fun c ↦ hP1 (f c))
    (fun c ↦ hR1 (g c)) α'.continuous β'.continuous continuous_id
    (P.continuous.comp (continuous_snd.prodMk (hf.comp continuous_fst)))
    (R.continuous.comp (continuous_snd.prodMk (hg.comp continuous_fst)))
  let Γ' : C(DMC (α ∘ f) (β ∘ g), DMC (α' ∘ (α ∘ f)) (β' ∘ (β ∘ g))) :=
    phiCM α' β' id (fun c _ ↦ α' (α (f c))) (fun c _ ↦ β' (β (g c))) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) α'.continuous β'.continuous continuous_id
      ((α'.continuous.comp hαf).comp continuous_fst) ((β'.continuous.comp hβg).comp continuous_fst)
  let Ψ' : C(DMC (α' ∘ (α ∘ f)) (β' ∘ (β ∘ g)), DMC (α ∘ f) (β ∘ g)) :=
    phiCM α β id (fun c r ↦ P' (r, (α ∘ f) c)) (fun c r ↦ R' (r, (β ∘ g) c))
      (fun c ↦ hP0' _) (fun c ↦ hR0' _) (fun c ↦ hP1' _) (fun c ↦ hR1' _)
      α.continuous β.continuous continuous_id
      (P'.continuous.comp (continuous_snd.prodMk (hαf.comp continuous_fst)))
      (R'.continuous.comp (continuous_snd.prodMk (hβg.comp continuous_fst)))
  let E : C(DMC (α' ∘ (α ∘ f)) (β' ∘ (β ∘ g)), DMC f g) :=
    phiCM id id id (fun c r ↦ P (r, f c)) (fun c r ↦ R (r, g c)) (fun c ↦ hP0 (f c))
      (fun c ↦ hR0 (g c)) (fun c ↦ hP1 (f c)) (fun c ↦ hR1 (g c)) continuous_id continuous_id
      continuous_id (P.continuous.comp (continuous_snd.prodMk (hf.comp continuous_fst)))
      (R.continuous.comp (continuous_snd.prodMk (hg.comp continuous_fst)))
  let Einv : C(DMC f g, DMC (α' ∘ (α ∘ f)) (β' ∘ (β ∘ g))) :=
    phiCM id id id (fun c r ↦ P (symm r, f c)) (fun c r ↦ R (symm r, g c))
      (fun c ↦ by simp [hP1]) (fun c ↦ by simp [hR1]) (fun c ↦ by simp [hP0])
      (fun c ↦ by simp [hR0]) continuous_id continuous_id continuous_id
      (P.continuous.comp (((continuous_symm.comp continuous_snd).prodMk
        (hf.comp continuous_fst))))
      (R.continuous.comp (((continuous_symm.comp continuous_snd).prodMk
        (hg.comp continuous_fst))))
  have ha : (Ψ.comp Γ).Homotopic (ContinuousMap.id _) :=
    ends_left_inv α α' β β' α.continuous α'.continuous β.continuous β'.continuous P R
      P.continuous R.continuous hP0 hP1 hR0 hR1 hf hg Γ Ψ (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hb : (Ψ'.comp Γ').Homotopic (ContinuousMap.id _) :=
    ends_left_inv (f := α ∘ f) (g := β ∘ g) α' α β' β α'.continuous α.continuous
      β'.continuous β.continuous P' R' P'.continuous R'.continuous hP0' hP1' hR0' hR1'
      hαf hβg Γ' Ψ' (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hc : (E.comp Γ').Homotopic Ψ :=
    ends_comparison α α' β β' α.continuous β.continuous α'.continuous β'.continuous P R
      P.continuous R.continuous
      hP0 hP1 hR0 hR1 hf hg Γ' E Ψ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hd : (Einv.comp E).Homotopic (ContinuousMap.id _) :=
    rev_comp_homotopic (fun c r ↦ P (r, f c)) (fun c r ↦ R (r, g c))
      (P.continuous.comp (continuous_snd.prodMk (hf.comp continuous_fst)))
      (R.continuous.comp (continuous_snd.prodMk (hg.comp continuous_fst)))
      (fun c ↦ hP0 (f c)) (fun c ↦ hP1 (f c)) (fun c ↦ hR0 (g c)) (fun c ↦ hR1 (g c))
      E Einv (fun _ ↦ rfl) (fun _ ↦ rfl)
  refine nonempty_homotopyEquiv_of_left_right Ψ (Ψ'.comp Einv) Γ ?_ ha
  have h1 : ((Ψ'.comp Einv).comp Ψ).Homotopic ((Ψ'.comp Einv).comp (E.comp Γ')) :=
    (ContinuousMap.Homotopic.refl _).comp hc.symm
  have h2 : ((Ψ'.comp Einv).comp (E.comp Γ')) = Ψ'.comp ((Einv.comp E).comp Γ') := by
    simp only [ContinuousMap.comp_assoc]
  have h3 : (Ψ'.comp ((Einv.comp E).comp Γ')).Homotopic (Ψ'.comp Γ') := by
    simpa using (ContinuousMap.Homotopic.refl Ψ').comp (hd.comp (ContinuousMap.Homotopic.refl Γ'))
  exact h1.trans (h2 ▸ h3.trans hb)

section Mid

variable {C' : Type*} [TopologicalSpace C']

/-- Right inverse of the map induced by a map of the middle spaces. -/
private lemma mid_right_inv (F : C' → A) (G : C' → B) (hF : Continuous F) (hG : Continuous G)
    (δ : C → C') (δ' : C' → C) (hδ : Continuous δ) (hδ' : Continuous δ')
    (L : I × C' → C') (hL : Continuous L) (hL0 : ∀ y, L (0, y) = δ (δ' y))
    (hL1 : ∀ y, L (1, y) = y)
    (Γ : C(DMC (F ∘ δ) (G ∘ δ), DMC F G)) (Ψ : C(DMC F G, DMC (F ∘ δ) (G ∘ δ)))
    (hΓ : ∀ x, Γ x = phi id id δ (fun c _ ↦ F (δ c)) (fun c _ ↦ G (δ c)) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) x)
    (hΨ : ∀ x, Ψ x = phi id id δ' (fun y r ↦ F (L (symm r, y))) (fun y r ↦ G (L (symm r, y)))
      (fun y ↦ by simp [hL1]) (fun y ↦ by simp [hL1]) (fun y ↦ by simp [hL0])
      (fun y ↦ by simp [hL0]) x) :
    (Γ.comp Ψ).Homotopic (ContinuousMap.id _) := by
  have hLs : Continuous fun p : C' × I ↦ L (symm p.2, p.1) :=
    hL.comp ((continuous_symm.comp continuous_snd).prodMk continuous_fst)
  refine (comp_homotopic (F := Ψ) (F' := Γ) (G := compCM (f := F) (g := G) (f' := F ∘ δ)
      (g' := G ∘ δ) (f'' := F) (g'' := G) id id δ' (fun y r ↦ F (L (symm r, y)))
      (fun y r ↦ G (L (symm r, y))) (fun y ↦ by simp [hL1]) (fun y ↦ by simp [hL1])
      (fun y ↦ by simp [hL0]) (fun y ↦ by simp [hL0]) id id δ (fun c _ ↦ F (δ c))
      (fun c _ ↦ G (δ c)) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
      continuous_id continuous_id hδ' (hF.comp hLs) (hG.comp hLs) continuous_id continuous_id hδ
      ((hF.comp hδ).comp continuous_fst) ((hG.comp hδ).comp continuous_fst))
    id id δ' (fun y r ↦ F (L (symm r, y))) (fun y r ↦ G (L (symm r, y)))
    (fun y ↦ by simp [hL1]) (fun y ↦ by simp [hL1]) (fun y ↦ by simp [hL0])
    (fun y ↦ by simp [hL0]) id id δ (fun c _ ↦ F (δ c)) (fun c _ ↦ G (δ c)) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) hΨ hΓ (fun _ ↦ rfl)).trans ?_
  let τ : I → I → I := fun s r ↦ cl (max (s : ℝ) (1 - 2 * r))
  have hτ0 : ∀ s, τ s 0 = 1 := fun s ↦ by
    simp only [τ, Set.Icc.coe_zero, mul_zero, sub_zero]
    rw [max_eq_right s.2.2, cl_one]
  have hτ1 : ∀ s, τ s 1 = s := fun s ↦ by
    simp only [τ, Set.Icc.coe_one]
    rw [max_eq_left (by linarith [s.2.1]), cl_coe]
  have hτc : Continuous fun p : I × C' × I ↦ τ p.1 p.2.2 := by
    have hs : Continuous fun p : I × C' × I ↦ ((p.1 : I) : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have ht : Continuous fun p : I × C' × I ↦ ((p.2.2 : I) : ℝ) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact continuous_cl.comp (hs.max (continuous_const.sub (continuous_const.mul ht)))
  have hLτ : Continuous fun p : I × C' × I ↦ L (τ p.1 p.2.2, p.2.1) :=
    hL.comp (hτc.prodMk (continuous_fst.comp continuous_snd))
  have e0 : ∀ (s : I) (y : C'), F (L (τ s 0, y)) = id (F y) := fun s y ↦ by rw [hτ0, hL1]; rfl
  have e0' : ∀ (s : I) (y : C'), G (L (τ s 0, y)) = id (G y) := fun s y ↦ by rw [hτ0, hL1]; rfl
  have e1 : ∀ (s : I) (y : C'), F (L (τ s 1, y)) = F (L (s, y)) := fun s y ↦ by rw [hτ1]
  have e1' : ∀ (s : I) (y : C'), G (L (τ s 1, y)) = G (L (s, y)) := fun s y ↦ by rw [hτ1]
  refine (homotopic_of_family (F₁ := thirdCM) (fun _ ↦ id) (fun _ ↦ id) (fun s y ↦ L (s, y))
    (fun s y r ↦ F (L (τ s r, y))) (fun s y r ↦ G (L (τ s r, y)))
    e0 e0' e1 e1' continuous_snd continuous_snd hL (hF.comp hLτ) (hG.comp hLτ) ?_ ?_).trans
    thirdCM_homotopic
  · intro x
    simp only [compCM, phiCM_apply]
    refine phi_congr (fun _ ↦ rfl) (fun _ ↦ rfl) (fun y ↦ (hL0 y).symm) (fun y r ↦ ?_)
      (fun y r ↦ ?_) x
    · simp only [concat, τ, Set.Icc.coe_zero, id, Function.comp]
      split_ifs with h
      · congr 2
        refine Prod.ext (Subtype.ext ?_) rfl
        rw [coe_symm_eq, coe_cl (by linarith [r.2.1]) (by linarith),
          coe_cl (le_max_left _ _) (max_le (by norm_num) (by linarith [r.2.1])),
          max_eq_right (by linarith)]
      · rw [max_eq_left (by linarith), cl_zero, hL0]
    · simp only [concat, τ, Set.Icc.coe_zero, id, Function.comp]
      split_ifs with h
      · congr 2
        refine Prod.ext (Subtype.ext ?_) rfl
        rw [coe_symm_eq, coe_cl (by linarith [r.2.1]) (by linarith),
          coe_cl (le_max_left _ _) (max_le (by norm_num) (by linarith [r.2.1])),
          max_eq_right (by linarith)]
      · rw [max_eq_left (by linarith), cl_zero, hL0]
  · intro x
    rw [← phi_const_eq]
    refine phi_congr (fun _ ↦ rfl) (fun _ ↦ rfl) (fun y ↦ (hL1 y).symm) (fun y r ↦ ?_)
      (fun y r ↦ ?_) x
    · simp only [τ, Set.Icc.coe_one]
      rw [max_eq_left (by linarith [r.2.1]), cl_one, hL1]
    · simp only [τ, Set.Icc.coe_one]
      rw [max_eq_left (by linarith [r.2.1]), cl_one, hL1]

/-- The composite of two maps of the middle spaces is homotopic to the homotopy map along
`L : δ ≃ id`. -/
private lemma mid_comparison (F : C' → A) (G : C' → B) (hF : Continuous F) (hG : Continuous G)
    (δ : C → C') (δ' : C' → C) (hδ : Continuous δ) (hδ' : Continuous δ')
    (L : I × C' → C') (hL : Continuous L) (hL0 : ∀ y, L (0, y) = δ (δ' y))
    (hL1 : ∀ y, L (1, y) = y)
    (Γ₁ : C(DMC ((F ∘ δ) ∘ δ') ((G ∘ δ) ∘ δ'), DMC (F ∘ δ) (G ∘ δ)))
    (Γ₂ : C(DMC (F ∘ δ) (G ∘ δ), DMC F G))
    (E : C(DMC ((F ∘ δ) ∘ δ') ((G ∘ δ) ∘ δ'), DMC F G))
    (hΓ₁ : ∀ x, Γ₁ x = phi id id δ' (fun y _ ↦ F (δ (δ' y))) (fun y _ ↦ G (δ (δ' y)))
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) x)
    (hΓ₂ : ∀ x, Γ₂ x = phi id id δ (fun c _ ↦ F (δ c)) (fun c _ ↦ G (δ c)) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) x)
    (hE : ∀ x, E x = phi id id id (fun y r ↦ F (L (r, y))) (fun y r ↦ G (L (r, y)))
      (fun y ↦ by simp [hL0]) (fun y ↦ by simp [hL0]) (fun y ↦ by simp [hL1])
      (fun y ↦ by simp [hL1]) x) :
    (Γ₂.comp Γ₁).Homotopic E := by
  refine (comp_homotopic (F := Γ₁) (F' := Γ₂) (G := compCM (f := (F ∘ δ) ∘ δ')
      (g := (G ∘ δ) ∘ δ') (f' := F ∘ δ) (g' := G ∘ δ) (f'' := F) (g'' := G) id id δ'
      (fun y _ ↦ F (δ (δ' y))) (fun y _ ↦ G (δ (δ' y))) (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl) id id δ (fun c _ ↦ F (δ c)) (fun c _ ↦ G (δ c))
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) continuous_id continuous_id hδ'
      (((hF.comp hδ).comp hδ').comp continuous_fst) (((hG.comp hδ).comp hδ').comp continuous_fst)
      continuous_id continuous_id hδ ((hF.comp hδ).comp continuous_fst)
      ((hG.comp hδ).comp continuous_fst))
    id id δ' (fun y _ ↦ F (δ (δ' y))) (fun y _ ↦ G (δ (δ' y))) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ ↦ rfl) id id δ (fun c _ ↦ F (δ c)) (fun c _ ↦ G (δ c))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) hΓ₁ hΓ₂ (fun _ ↦ rfl)).trans ?_
  let τ : I → I → I := fun s r ↦ cl (s * r)
  have hτ0 : ∀ s, τ s 0 = 0 := fun s ↦ by simp [τ, cl_zero]
  have hτ1 : ∀ s, τ s 1 = s := fun s ↦ by simp [τ, cl_coe]
  have hτc : Continuous fun p : I × C' × I ↦ τ p.1 p.2.2 :=
    continuous_cl.comp ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  have hLτ : Continuous fun p : I × C' × I ↦ L (τ p.1 p.2.2, p.2.1) :=
    hL.comp (hτc.prodMk (continuous_fst.comp continuous_snd))
  have e0 : ∀ (s : I) (y : C'), F (L (τ s 0, y)) = id (((F ∘ δ) ∘ δ') y) := fun s y ↦ by
    rw [hτ0, hL0]; rfl
  have e0' : ∀ (s : I) (y : C'), G (L (τ s 0, y)) = id (((G ∘ δ) ∘ δ') y) := fun s y ↦ by
    rw [hτ0, hL0]; rfl
  have e1 : ∀ (s : I) (y : C'), F (L (τ s 1, y)) = F (L (s, y)) := fun s y ↦ by rw [hτ1]
  have e1' : ∀ (s : I) (y : C'), G (L (τ s 1, y)) = G (L (s, y)) := fun s y ↦ by rw [hτ1]
  refine homotopic_of_family (fun _ ↦ id) (fun _ ↦ id) (fun s y ↦ L (s, y))
    (fun s y r ↦ F (L (τ s r, y))) (fun s y r ↦ G (L (τ s r, y)))
    e0 e0' e1 e1' continuous_snd continuous_snd hL (hF.comp hLτ) (hG.comp hLτ) ?_ ?_
  · intro x
    simp only [compCM, phiCM_apply]
    refine phi_congr (fun _ ↦ rfl) (fun _ ↦ rfl) (fun y ↦ (hL0 y).symm) (fun y r ↦ ?_)
      (fun y r ↦ ?_) x
    · simp only [concat, τ, Set.Icc.coe_zero, zero_mul, cl_zero, hL0, id, Function.comp]
      split_ifs <;> rfl
    · simp only [concat, τ, Set.Icc.coe_zero, zero_mul, cl_zero, hL0, id, Function.comp]
      split_ifs <;> rfl
  · intro x
    rw [hE]
    refine phi_congr (fun _ ↦ rfl) (fun _ ↦ rfl) (fun y ↦ (hL1 y).symm) (fun y r ↦ ?_)
      (fun y r ↦ ?_) x
    · simp only [τ, Set.Icc.coe_one, one_mul, cl_coe]
    · simp only [τ, Set.Icc.coe_one, one_mul, cl_coe]

/-- **Replacing the middle**: a homotopy equivalence `e : C ≃ C'` gives a homotopy equivalence
`D(F ∘ e, G ∘ e) ≃ D(F, G)`. -/
private lemma nonempty_homotopyEquiv_mid (e : ContinuousMap.HomotopyEquiv C C')
    (F : C' → A) (G : C' → B) (hF : Continuous F) (hG : Continuous G) :
    Nonempty (ContinuousMap.HomotopyEquiv (DMC (F ∘ e.toFun) (G ∘ e.toFun)) (DMC F G)) := by
  set γ := e.toFun
  set γ' := e.invFun
  obtain ⟨Q⟩ := e.left_inv
  obtain ⟨L⟩ := e.right_inv
  have hQ0 : ∀ c, Q (0, c) = γ' (γ c) := fun c ↦ Q.apply_zero c
  have hQ1 : ∀ c, Q (1, c) = c := fun c ↦ Q.apply_one c
  have hL0 : ∀ y, L (0, y) = γ (γ' y) := fun y ↦ L.apply_zero y
  have hL1 : ∀ y, L (1, y) = y := fun y ↦ L.apply_one y
  have hFγ : Continuous (F ∘ γ) := hF.comp γ.continuous
  have hGγ : Continuous (G ∘ γ) := hG.comp γ.continuous
  have hQs : Continuous fun p : C × I ↦ Q (symm p.2, p.1) :=
    Q.continuous.comp ((continuous_symm.comp continuous_snd).prodMk continuous_fst)
  have hLc : Continuous fun p : C' × I ↦ L (p.2, p.1) :=
    L.continuous.comp (continuous_snd.prodMk continuous_fst)
  have hLs : Continuous fun p : C' × I ↦ L (symm p.2, p.1) :=
    L.continuous.comp ((continuous_symm.comp continuous_snd).prodMk continuous_fst)
  let Γ₁ : C(DMC ((F ∘ γ) ∘ γ') ((G ∘ γ) ∘ γ'), DMC (F ∘ γ) (G ∘ γ)) :=
    phiCM id id γ' (fun y _ ↦ F (γ (γ' y))) (fun y _ ↦ G (γ (γ' y))) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) continuous_id continuous_id γ'.continuous
      (((hF.comp γ.continuous).comp γ'.continuous).comp continuous_fst)
      (((hG.comp γ.continuous).comp γ'.continuous).comp continuous_fst)
  let Ψ₁ : C(DMC (F ∘ γ) (G ∘ γ), DMC ((F ∘ γ) ∘ γ') ((G ∘ γ) ∘ γ')) :=
    phiCM id id γ (fun c r ↦ (F ∘ γ) (Q (symm r, c))) (fun c r ↦ (G ∘ γ) (Q (symm r, c)))
      (fun c ↦ by simp [hQ1]) (fun c ↦ by simp [hQ1]) (fun c ↦ by simp [hQ0])
      (fun c ↦ by simp [hQ0]) continuous_id continuous_id γ.continuous (hFγ.comp hQs)
      (hGγ.comp hQs)
  let Γ₂ : C(DMC (F ∘ γ) (G ∘ γ), DMC F G) :=
    phiCM id id γ (fun c _ ↦ F (γ c)) (fun c _ ↦ G (γ c)) (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl) continuous_id continuous_id γ.continuous
      (hFγ.comp continuous_fst) (hGγ.comp continuous_fst)
  let E : C(DMC ((F ∘ γ) ∘ γ') ((G ∘ γ) ∘ γ'), DMC F G) :=
    phiCM id id id (fun y r ↦ F (L (r, y))) (fun y r ↦ G (L (r, y)))
      (fun y ↦ by simp [hL0]) (fun y ↦ by simp [hL0]) (fun y ↦ by simp [hL1])
      (fun y ↦ by simp [hL1]) continuous_id continuous_id continuous_id (hF.comp hLc)
      (hG.comp hLc)
  let Einv : C(DMC F G, DMC ((F ∘ γ) ∘ γ') ((G ∘ γ) ∘ γ')) :=
    phiCM id id id (fun y r ↦ F (L (symm r, y))) (fun y r ↦ G (L (symm r, y)))
      (fun y ↦ by simp [hL1]) (fun y ↦ by simp [hL1]) (fun y ↦ by simp [hL0])
      (fun y ↦ by simp [hL0]) continuous_id continuous_id continuous_id (hF.comp hLs)
      (hG.comp hLs)
  have ha : (Γ₁.comp Ψ₁).Homotopic (ContinuousMap.id _) :=
    mid_right_inv (F ∘ γ) (G ∘ γ) hFγ hGγ γ' γ γ'.continuous γ.continuous Q Q.continuous hQ0
      hQ1 Γ₁ Ψ₁ (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hb : (Γ₂.comp Γ₁).Homotopic E :=
    mid_comparison F G hF hG γ γ' γ.continuous γ'.continuous L L.continuous hL0 hL1 Γ₁ Γ₂ E
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hc : (Einv.comp E).Homotopic (ContinuousMap.id _) :=
    rev_comp_homotopic (fun y r ↦ F (L (r, y))) (fun y r ↦ G (L (r, y))) (hF.comp hLc)
      (hG.comp hLc) (fun y ↦ by simp [hL0]) (fun y ↦ by simp [hL1]) (fun y ↦ by simp [hL0])
      (fun y ↦ by simp [hL1]) E Einv (fun _ ↦ rfl) (fun _ ↦ rfl)
  have h1 : Nonempty (ContinuousMap.HomotopyEquiv (DMC ((F ∘ γ) ∘ γ') ((G ∘ γ) ∘ γ'))
      (DMC (F ∘ γ) (G ∘ γ))) := by
    refine nonempty_homotopyEquiv_of_left_right Γ₁ (Einv.comp Γ₂) Ψ₁ ?_ ha
    rw [ContinuousMap.comp_assoc]
    exact ((ContinuousMap.Homotopic.refl Einv).comp hb).trans hc
  obtain ⟨e1⟩ := h1
  obtain ⟨e2⟩ : Nonempty (ContinuousMap.HomotopyEquiv (DMC ((F ∘ γ) ∘ γ') ((G ∘ γ) ∘ γ'))
      (DMC F G)) :=
    nonempty_homotopyEquiv_of_homotopy (fun y r ↦ F (L (r, y))) (fun y r ↦ G (L (r, y)))
      (hF.comp hLc) (hG.comp hLc) (fun y ↦ by simp [hL0]) (fun y ↦ by simp [hL1])
      (fun y ↦ by simp [hL0]) (fun y ↦ by simp [hL1])
  exact ⟨e1.symm.trans e2⟩

end Mid

end Invariance

section Collar

open CategoryTheory

variable {Bc M Y : Type*} [TopologicalSpace Bc] [TopologicalSpace M] [TopologicalSpace Y]

/-- Extension of a function on a collar `c : Bc × [0, 1) → M` by a function `u` on `M`. -/
private def collarExtend (c : Bc × Set.Ico (0 : ℝ) 1 → M) (u : M → Y)
    (g : Bc × Set.Ico (0 : ℝ) 1 → Y) (m : M) : Y := by
  classical
  exact if h : m ∈ Set.range c then g h.choose else u m

private lemma collarExtend_apply {c : Bc × Set.Ico (0 : ℝ) 1 → M} (hc : Function.Injective c)
    (u : M → Y) (g : Bc × Set.Ico (0 : ℝ) 1 → Y) (p : Bc × Set.Ico (0 : ℝ) 1) :
    collarExtend c u g (c p) = g p := by
  have h : c p ∈ Set.range c := ⟨p, rfl⟩
  rw [collarExtend, dif_pos h, hc h.choose_spec]

private lemma collarExtend_of_notMem {c : Bc × Set.Ico (0 : ℝ) 1 → M} (u : M → Y)
    (g : Bc × Set.Ico (0 : ℝ) 1 → Y) {m : M} (hm : m ∉ Set.range c) :
    collarExtend c u g m = u m := by
  rw [collarExtend, dif_neg hm]

/-- A function on a collar agreeing with `u` beyond the half-collar extends continuously by
`u`. -/
private lemma continuous_collarExtend [CompactSpace Bc] [T2Space M]
    {c : Bc × Set.Ico (0 : ℝ) 1 → M} (hc : IsOpenEmbedding c) (u : M → Y) (hu : Continuous u)
    (g : Bc × Set.Ico (0 : ℝ) 1 → Y) (hg : Continuous g)
    (hgu : ∀ p, 1 / 2 < (p.2 : ℝ) → g p = u (c p)) : Continuous (collarExtend c u g) := by
  -- the closed half-collar
  let k : Bc × Set.Icc (0 : ℝ) (1 / 2) → M := fun q ↦
    c (q.1, ⟨q.2, q.2.2.1, by linarith [q.2.2.2]⟩)
  have hk : Continuous k := hc.continuous.comp (continuous_fst.prodMk
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _))
  have hK : IsClosed (Set.range k) := (isCompact_range hk).isClosed
  have hKsub : ∀ m ∈ Set.range c, m ∉ Set.range k → ∀ p, c p = m → 1 / 2 < (p.2 : ℝ) := by
    rintro m - hmk p rfl
    by_contra hle
    exact hmk ⟨(p.1, ⟨p.2, p.2.2.1, not_lt.1 hle⟩), rfl⟩
  refine continuous_iff_continuousAt.2 fun m ↦ ?_
  by_cases hm : m ∈ Set.range c
  · -- on the open set `range c`, the extension is `g ∘ c⁻¹`
    have hopen : IsOpen (Set.range c) := hc.isOpen_range
    have hcont : ContinuousOn (collarExtend c u g) (Set.range c) := by
      rw [continuousOn_iff_continuous_restrict]
      let e := hc.isEmbedding.toHomeomorph
      have : ∀ y : Set.range c, g (e.symm y) = collarExtend c u g y := by
        intro y
        obtain ⟨p, hp⟩ := y.2
        have hy : y = e p := Subtype.ext hp.symm
        rw [hy, Homeomorph.symm_apply_apply]
        exact (collarExtend_apply hc.injective u g p).symm
      exact (hg.comp e.symm.continuous).congr this
    exact hcont.continuousAt (hopen.mem_nhds hm)
  · -- off the closed half-collar, the extension is `u`
    have hmk : m ∉ Set.range k := fun ⟨q, hq⟩ ↦ hm ⟨_, hq⟩
    have heq : ∀ m' ∈ (Set.range k)ᶜ, collarExtend c u g m' = u m' := by
      intro m' hm'
      by_cases hm'c : m' ∈ Set.range c
      · obtain ⟨p, rfl⟩ := hm'c
        rw [collarExtend_apply hc.injective]
        exact hgu p (hKsub _ ⟨p, rfl⟩ hm' p rfl)
      · exact collarExtend_of_notMem u g hm'c
    exact (hu.continuousAt.congr (Filter.eventuallyEq_of_mem (hK.isOpen_compl.mem_nhds hmk)
      fun m' hm' ↦ (heq m' hm').symm))

end Collar

/-- Clamp a real number into `[0, 1/2] ⊆ [0, 1)`. -/
private def half (r : ℝ) : Set.Ico (0 : ℝ) 1 :=
  ⟨max 0 (min r (1 / 2)), le_max_left _ _, max_lt (by norm_num)
    (by linarith [min_le_right r (1 / 2)])⟩

private lemma continuous_half : Continuous half :=
  Continuous.subtype_mk (continuous_const.max (continuous_id.min continuous_const)) _

private lemma coe_half {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) : (half r : ℝ) = r := by
  show max 0 (min r (1 / 2)) = r
  rw [min_eq_left h1, max_eq_right h0]

private lemma half_eq {r : ℝ} (t : Set.Ico (0 : ℝ) 1) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2)
    (h : (t : ℝ) = r) : half r = t := Subtype.ext (by rw [coe_half h0 h1, h])

section Pushout

open CategoryTheory

variable {M : Type} [TopologicalSpace M] [T2Space M] {Bs : Set M} [CompactSpace Bs]
  {X : Type} [TopologicalSpace X] {Ss : Set X}

/-- **Collars absorb cylinders**: if `X` is the pushout of `∂M ⊆ M` along `φ : ∂M → S` and
`∂M` has a collar in `M`, then `X` is homeomorphic to the double mapping cylinder of `∂M ⊆ M`
and `φ`. -/
private lemma nonempty_homeomorph_dmc (φ : C(Bs, Ss)) (κ : C(M, X))
    (hpush : IsPushout
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Bs ⟶ TopCat.of M)
      (TopCat.ofHom φ) (TopCat.ofHom κ)
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Ss ⟶ TopCat.of X))
    (hsurj : ∀ y : X, y ∈ Ss ∨ ∃ m, κ m = y)
    (c : Bs × Set.Ico (0 : ℝ) 1 → M) (hc : IsOpenEmbedding c)
    (hc0 : ∀ (x : Bs) (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (x, t) = x) :
    Nonempty (X ≃ₜ DMC (Subtype.val : Bs → M) (φ : Bs → Ss)) := by
  have hcomm : ∀ b : Bs, κ b = (φ b : X) := fun b ↦ ConcreteCategory.congr_hom hpush.w b
  have hc0' : ∀ x : Bs, c (x, half 0) = x := fun x ↦ hc0 x _ (coe_half le_rfl (by norm_num))
  -- the map `M → D`
  let gσ : Bs × Set.Ico (0 : ℝ) 1 → DMC (Subtype.val : Bs → M) (φ : Bs → Ss) := fun p ↦
    if (p.2 : ℝ) ≤ 1 / 4 then cyl p.1 (cl (1 - 4 * p.2))
    else if (p.2 : ℝ) ≤ 1 / 2 then inA (c (p.1, half (2 * p.2 - 1 / 2))) else inA (c p)
  have hgσ : Continuous gσ := by
    have ht : Continuous fun p : Bs × Set.Ico (0 : ℝ) 1 ↦ ((p.2 : Set.Ico (0 : ℝ) 1) : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    refine Continuous.if_le (continuous_cyl.comp (continuous_fst.prodMk (continuous_cl.comp
      (continuous_const.sub (continuous_const.mul ht))))) (Continuous.if_le
      (continuous_inA.comp (hc.continuous.comp (continuous_fst.prodMk (continuous_half.comp
        ((continuous_const.mul ht).sub continuous_const)))))
      (continuous_inA.comp hc.continuous) ht continuous_const ?_) ht continuous_const ?_
    · intro p hp
      congr 2
      exact Prod.ext rfl (half_eq _ (by norm_num [hp]) (by norm_num [hp])
        (by norm_num [hp]))
    · intro p hp
      rw [if_pos (by norm_num [hp]), show (1 : ℝ) - 4 * p.2 = 0 by norm_num [hp], cl_zero,
        cyl_zero, show (2 : ℝ) * p.2 - 1 / 2 = 0 by norm_num [hp], hc0']
  let σM : M → DMC (Subtype.val : Bs → M) (φ : Bs → Ss) := collarExtend c inA gσ
  have hσM : Continuous σM := continuous_collarExtend hc inA continuous_inA gσ hgσ
    (fun p hp ↦ by simp only [gσ, if_neg (show ¬ (p.2 : ℝ) ≤ 1 / 4 by linarith),
      if_neg (not_le.2 hp)])
  have hσMb : ∀ x : Bs, σM x = inB (φ x) := fun x ↦ by
    rw [← hc0' x, show σM (c (x, half 0)) = gσ (x, half 0) from
      collarExtend_apply hc.injective _ _ _]
    simp only [gσ, coe_half le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num [cl_one, cyl_one]
  let sgm : X → DMC (Subtype.val : Bs → M) (φ : Bs → Ss) :=
    ConcreteCategory.hom (hpush.desc (TopCat.ofHom ⟨σM, hσM⟩)
      (TopCat.ofHom ⟨fun s ↦ inB s, continuous_inB⟩) (by
        ext x
        exact hσMb x))
  have hsigc : Continuous sgm := (ConcreteCategory.hom (hpush.desc _ _ _)).continuous
  have hsigκ : ∀ m, sgm (κ m) = σM m := fun m ↦
    ConcreteCategory.congr_hom (hpush.inl_desc _ _ _) m
  have hsigS : ∀ s : Ss, sgm s = inB s := fun s ↦
    ConcreteCategory.congr_hom (hpush.inr_desc _ _ _) s
  -- the map `D → X`
  let gπ : Bs × Set.Ico (0 : ℝ) 1 → X := fun p ↦
    if (p.2 : ℝ) ≤ 1 / 2 then κ (c (p.1, half (p.2 / 2 + 1 / 4))) else κ (c p)
  have hgπ : Continuous gπ := by
    have ht : Continuous fun p : Bs × Set.Ico (0 : ℝ) 1 ↦ ((p.2 : Set.Ico (0 : ℝ) 1) : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    refine Continuous.if_le (κ.continuous.comp (hc.continuous.comp (continuous_fst.prodMk
      (continuous_half.comp ((ht.div_const _).add continuous_const)))))
      (κ.continuous.comp hc.continuous) ht continuous_const ?_
    intro p hp
    congr 2
    exact Prod.ext rfl (half_eq _ (by norm_num [hp]) (by norm_num [hp])
      (by norm_num [hp]))
  let κ' : M → X := collarExtend c κ gπ
  have hκ' : Continuous κ' := continuous_collarExtend hc κ κ.continuous gπ hgπ
    (fun p hp ↦ by simp only [gπ, if_neg (not_le.2 hp)])
  let prj : DMC (Subtype.val : Bs → M) (φ : Bs → Ss) → X :=
    desc κ' (fun s ↦ (s : X)) (fun x t ↦ κ (c (x, half ((1 - t) / 4))))
      (fun x ↦ by
        change _ = κ' (x : M)
        rw [← hc0' x, show κ' (c (x, half 0)) = gπ (x, half 0) from
          collarExtend_apply hc.injective _ _ _]
        simp only [gπ, coe_half le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        norm_num)
      (fun x ↦ by
        change _ = ((φ x : Ss) : X)
        rw [← hcomm, show (1 : ℝ) - ((1 : I) : ℝ) = 0 by simp, zero_div, hc0'])
  have hprc : Continuous prj := continuous_desc hκ' continuous_subtype_val
    (κ.continuous.comp (hc.continuous.comp (continuous_fst.prodMk (continuous_half.comp
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).div_const _)))))
  -- the two maps are inverse
  have hprsig : ∀ y, prj (sgm y) = y := by
    intro y
    rcases hsurj y with hy | ⟨m, rfl⟩
    · rw [show y = ((⟨y, hy⟩ : Ss) : X) from rfl, hsigS]; rfl
    rw [hsigκ]
    by_cases hm : m ∈ Set.range c
    · obtain ⟨⟨x, τ⟩, rfl⟩ := hm
      have hτ0 := τ.2.1
      change prj (collarExtend c inA gσ (c (x, τ))) = κ (c (x, τ))
      rw [collarExtend_apply hc.injective]
      simp only [gσ]
      split_ifs with h1 h2
      · change κ (c (x, half ((1 - (cl (1 - 4 * τ) : ℝ)) / 4))) = _
        rw [coe_cl (by linarith) (by linarith)]
        congr 2
        exact Prod.ext rfl (half_eq _ (by linarith) (by linarith) (by ring))
      · show collarExtend c (⇑κ) gπ _ = _
        rw [collarExtend_apply hc.injective]
        simp only [gπ]
        rw [coe_half (by linarith) (by linarith), if_pos (by linarith)]
        congr 2
        exact Prod.ext rfl (half_eq _ (by linarith) (by linarith)
          (by dsimp only; ring))
      · show collarExtend c (⇑κ) gπ _ = _
        rw [collarExtend_apply hc.injective]
        simp only [gπ, if_neg h2]
    · change prj (collarExtend c inA gσ m) = κ m
      rw [collarExtend_of_notMem _ _ hm]
      show collarExtend c (⇑κ) gπ m = κ m
      exact collarExtend_of_notMem _ _ hm
  have hsigpr : ∀ d, sgm (prj d) = d := by
    intro d
    induction d using ind with
    | hA m =>
      show sgm (collarExtend c (⇑κ) gπ m) = inA m
      by_cases hm : m ∈ Set.range c
      · obtain ⟨⟨x, τ⟩, rfl⟩ := hm
        have hτ0 := τ.2.1
        rw [collarExtend_apply hc.injective]
        simp only [gπ]
        split_ifs with h1
        · rw [hsigκ]
          change collarExtend c inA gσ _ = _
          rw [collarExtend_apply hc.injective]
          simp only [gσ]
          rw [coe_half (by linarith) (by linarith)]
          split_ifs with h2 h3
          · have hτ : (τ : ℝ) = 0 := by linarith
            rw [show (1 : ℝ) - 4 * (τ / 2 + 1 / 4) = 0 by rw [hτ]; ring, cl_zero, cyl_zero]
            change inA (x : M) = _
            rw [hc0 x τ hτ]
          · congr 2
            exact Prod.ext rfl (half_eq _ (by linarith) (by linarith) (by ring))
          · exact absurd h3 (by linarith)
        · rw [hsigκ]
          change collarExtend c inA gσ _ = _
          rw [collarExtend_apply hc.injective]
          simp only [gσ, if_neg (show ¬ (τ : ℝ) ≤ 1 / 4 by linarith), if_neg h1]
      · rw [collarExtend_of_notMem _ _ hm, hsigκ]
        exact collarExtend_of_notMem _ _ hm
    | hB s => exact hsigS s
    | hC x t =>
      change sgm (κ (c (x, half ((1 - t) / 4)))) = cyl x t
      have ht0 := t.2.1
      have ht1 := t.2.2
      rw [hsigκ]
      change collarExtend c inA gσ _ = _
      rw [collarExtend_apply hc.injective]
      simp only [gσ]
      rw [coe_half (by linarith) (by linarith), if_pos (by linarith)]
      congr 1
      rw [show (1 : ℝ) - 4 * ((1 - t) / 4) = t by ring, cl_coe]
  exact ⟨Homeomorph.mk ⟨sgm, prj, hprsig, hsigpr⟩ hsigc hprc⟩

end Pushout

end DMC

end

end DmcPart

section RealPart

noncomputable section

section Realization

variable {V : Type*} [Fintype V]

/-- The closed face of the standard simplex in `V → ℝ` spanned by `σ`. -/
private def face (σ : Finset V) : Set (V → ℝ) :=
  {t | (∀ v, 0 ≤ t v) ∧ ∑ v, t v = 1 ∧ ∀ v ∉ σ, t v = 0}

private lemma convex_face (σ : Finset V) : Convex ℝ (face σ) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun v ↦ ?_, ?_, fun v hv ↦ ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 v)) (mul_nonneg hb (hy.1 v))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2.1, hy.2.1, mul_one, hab]
  · simp [hx.2.2 v hv, hy.2.2 v hv]

private lemma face_mono {σ τ : Finset V} (h : σ ⊆ τ) : face σ ⊆ face τ :=
  fun _ ht ↦ ⟨ht.1, ht.2.1, fun v hv ↦ ht.2.2 v fun hσ ↦ hv (h hσ)⟩

private lemma isClosed_face (σ : Finset V) : IsClosed (face σ) := by
  have h1 : IsClosed {t : V → ℝ | ∀ v, 0 ≤ t v} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun v ↦ isClosed_le continuous_const (continuous_apply v)
  have h2 : IsClosed {t : V → ℝ | ∑ v, t v = 1} :=
    isClosed_eq (continuous_finset_sum _ fun v _ ↦ continuous_apply v) continuous_const
  have h3 : IsClosed {t : V → ℝ | ∀ v ∉ σ, t v = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦
      isClosed_eq (continuous_apply v) continuous_const
  exact h1.inter (h2.inter h3)

private lemma isCompact_face (σ : Finset V) : IsCompact (face σ) :=
  (isCompact_stdSimplex ℝ V).of_isClosed_subset (isClosed_face σ) fun _ ht ↦ ⟨ht.1, ht.2.1⟩

private lemma exists_pos_of_mem_face {σ : Finset V} {t : V → ℝ} (ht : t ∈ face σ) :
    ∃ v ∈ σ, 0 < t v := by
  by_contra h
  push Not at h
  have : ∑ v, t v = 0 := Finset.sum_eq_zero fun v _ ↦ by
    by_cases hv : v ∈ σ
    · exact le_antisymm (h v hv) (ht.1 v)
    · exact ht.2.2 v hv
  rw [ht.2.1] at this
  exact one_ne_zero this

/-- The geometric realization in `V → ℝ` of a family `S` of simplices on the vertex set `V`. -/
private def realS (S : Set (Finset V)) : Set (V → ℝ) := ⋃ σ ∈ S, face σ

private lemma mem_realS {S : Set (Finset V)} {t : V → ℝ} :
    t ∈ realS S ↔ ∃ σ ∈ S, t ∈ face σ := by
  simp [realS]

private lemma isCompact_realS {S : Set (Finset V)} (hS : S.Finite) : IsCompact (realS S) :=
  hS.isCompact_biUnion fun σ _ ↦ isCompact_face σ

/-- The realization of a finite family of simplices is homotopy equivalent to the space of a
finite geometric simplicial complex: the open stars of the vertices form a good cover. -/
private lemma exists_simplicialComplex_homotopyEquiv_realS (S : Set (Finset V))
    (hS : S.Finite) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv (realS S) K.space) := by
  classical
  haveI : CompactSpace (realS S) := isCompact_iff_compactSpace.1 (isCompact_realS hS)
  let U : V → Set (realS S) := fun v ↦ {t | 0 < (t : V → ℝ) v}
  refine MMP.Topology.exists_homotopyEquiv_simplicialComplex_of_contractible_cover U
    (fun v ↦ isOpen_lt continuous_const ((continuous_apply v).comp continuous_subtype_val))
    (eq_univ_of_forall fun t ↦ ?_) fun I hI hne ↦ ?_
  · obtain ⟨σ, -, hσ⟩ := mem_realS.1 t.2
    obtain ⟨v, -, hv⟩ := exists_pos_of_mem_face hσ
    exact mem_iUnion.2 ⟨v, hv⟩
  · -- the intersection is star-convex about the barycenter of `I`
    obtain ⟨t₀, ht₀⟩ := hne
    simp only [mem_iInter, U, mem_setOf_eq] at ht₀
    obtain ⟨σ₀, hσ₀S, hσ₀⟩ := mem_realS.1 t₀.2
    have hIσ₀ : I ⊆ σ₀ := fun v hv ↦ by
      by_contra h
      have := hσ₀.2.2 v h
      linarith [ht₀ v hv]
    let b : V → ℝ := fun v ↦ if v ∈ I then (I.card : ℝ)⁻¹ else 0
    have hIc : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
    let Z : Set (V → ℝ) := {t | t ∈ realS S ∧ ∀ v ∈ I, 0 < t v}
    have hbZ : ∀ σ : Finset V, I ⊆ σ → b ∈ face σ := fun σ hσ ↦
      ⟨fun v ↦ by simp only [b]; split_ifs <;> positivity, by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ I)]
        simp only [b, Finset.filter_mem_eq_inter, Finset.univ_inter]
        rw [Finset.sum_congr rfl fun v hv ↦ if_pos hv,
          Finset.sum_congr rfl fun v (hv : v ∈ Finset.univ.filter (· ∉ I)) ↦
            if_neg (Finset.mem_filter.1 hv).2]
        simp [hIc.ne'], fun v hv ↦ by simp only [b]; rw [if_neg fun h ↦ hv (hσ h)]⟩
    have hstar : StarConvex ℝ b Z := by
      intro t ht a c ha hc hac
      obtain ⟨σ, hσS, hσ⟩ := mem_realS.1 ht.1
      have hIσ : I ⊆ σ := fun v hv ↦ by
        by_contra h
        have := hσ.2.2 v h
        linarith [ht.2 v hv]
      refine ⟨mem_realS.2 ⟨σ, hσS, convex_face σ (hbZ σ hIσ) hσ ha hc hac⟩, fun v hv ↦ ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, b, if_pos hv]
      rcases ha.lt_or_eq with ha' | ha'
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' (inv_pos.2 hIc))
          (mul_nonneg hc (ht.2 v hv).le)
      · rw [← ha'] at hac
        simp only [zero_add] at hac
        rw [← ha', hac]
        simpa using ht.2 v hv
    have hZ : Z.Nonempty := ⟨t₀, t₀.2, ht₀⟩
    haveI : ContractibleSpace Z := hstar.contractibleSpace hZ
    -- identify the intersection with `Z`
    let e : (⋂ i ∈ I, U i) ≃ₜ Z :=
      { toFun := fun t ↦ ⟨t.1.1, t.1.2, fun v hv ↦ mem_iInter₂.1 t.2 v hv⟩
        invFun := fun z ↦ ⟨⟨z.1, z.2.1⟩, mem_iInter₂.2 fun v hv ↦ z.2.2 v hv⟩
        left_inv := fun t ↦ rfl
        right_inv := fun z ↦ rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact e.toHomotopyEquiv.contractibleSpace

end Realization

section Cube

variable {V : Type*} [Fintype V]

/-- The cubical realization: points of `[0, 1]^V` with a coordinate `1`, supported on a member
of `S`. -/
private def cubeS (S : Set (Finset V)) : Set (V → ℝ) :=
  {u | (∀ v, 0 ≤ u v ∧ u v ≤ 1) ∧ (∃ v, u v = 1) ∧ ∃ σ ∈ S, ∀ v ∉ σ, u v = 0}

private lemma exists_eq_norm_of_nonneg [Nonempty V] {t : V → ℝ} (ht : ∀ v, 0 ≤ t v) :
    ∃ v, t v = ‖t‖ := by
  obtain ⟨v₀, -, hv₀⟩ := Finset.exists_max_image Finset.univ t Finset.univ_nonempty
  refine ⟨v₀, le_antisymm ?_ ?_⟩
  · simpa [Real.norm_of_nonneg (ht v₀)] using norm_le_pi_norm t v₀
  · refine (pi_norm_le_iff_of_nonneg (ht v₀)).2 fun v ↦ ?_
    rw [Real.norm_of_nonneg (ht v)]
    exact hv₀ v (Finset.mem_univ v)

private lemma norm_pos_of_mem_face {σ : Finset V} {t : V → ℝ} (ht : t ∈ face σ) : 0 < ‖t‖ := by
  obtain ⟨v, -, hv⟩ := exists_pos_of_mem_face ht
  exact hv.trans_le ((le_abs_self _).trans (norm_le_pi_norm t v))

private lemma norm_eq_one_of_mem_cubeS {S : Set (Finset V)} {u : V → ℝ} (hu : u ∈ cubeS S) :
    ‖u‖ = 1 := by
  obtain ⟨v, hv⟩ := hu.2.1
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun w ↦ ?_) ?_
  · rw [Real.norm_of_nonneg (hu.1 w).1]; exact (hu.1 w).2
  · simpa [hv] using norm_le_pi_norm u v

private lemma sum_pos_of_mem_cubeS {S : Set (Finset V)} {u : V → ℝ} (hu : u ∈ cubeS S) :
    0 < ∑ v, u v := by
  obtain ⟨v, hv⟩ := hu.2.1
  exact lt_of_lt_of_le (by rw [hv]; exact one_pos)
    (Finset.single_le_sum (fun w _ ↦ (hu.1 w).1) (Finset.mem_univ v))

/-- The realization of `S` is homeomorphic to its cubical realization. -/
private def realSHomeoCubeS (S : Set (Finset V)) : realS S ≃ₜ cubeS S where
  toFun t := ⟨‖(t : V → ℝ)‖⁻¹ • (t : V → ℝ), by
    obtain ⟨σ, hσS, hσ⟩ := mem_realS.1 t.2
    have hn := norm_pos_of_mem_face hσ
    haveI : Nonempty V := by
      obtain ⟨v, -, -⟩ := exists_pos_of_mem_face hσ; exact ⟨v⟩
    refine ⟨fun v ↦ ⟨?_, ?_⟩, ?_, σ, hσS, fun v hv ↦ ?_⟩
    · exact mul_nonneg (inv_nonneg.2 hn.le) (hσ.1 v)
    · rw [Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hn, mul_one]
      exact (le_abs_self _).trans (norm_le_pi_norm (t : V → ℝ) v)
    · obtain ⟨v, hv⟩ := exists_eq_norm_of_nonneg hσ.1
      exact ⟨v, by rw [Pi.smul_apply, smul_eq_mul, hv, inv_mul_cancel₀ hn.ne']⟩
    · simp [hσ.2.2 v hv]⟩
  invFun u := ⟨(∑ v, (u : V → ℝ) v)⁻¹ • (u : V → ℝ), by
    obtain ⟨-, -, σ, hσS, hσ⟩ := u.2
    have hs := sum_pos_of_mem_cubeS u.2
    refine mem_realS.2 ⟨σ, hσS, fun v ↦ ?_, ?_, fun v hv ↦ ?_⟩
    · exact mul_nonneg (inv_nonneg.2 hs.le) (u.2.1 v).1
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, inv_mul_cancel₀ hs.ne']
    · simp [hσ v hv]⟩
  left_inv t := by
    obtain ⟨σ, -, hσ⟩ := mem_realS.1 t.2
    have hn := norm_pos_of_mem_face hσ
    apply Subtype.ext
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hσ.2.1, mul_one, inv_inv]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  right_inv u := by
    have hs := sum_pos_of_mem_cubeS u.2
    apply Subtype.ext
    simp only
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hs.le, norm_eq_one_of_mem_cubeS u.2, mul_one,
      inv_inv, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  continuous_toFun := by
    have h0 : Continuous fun t : realS S ↦ ‖(t : V → ℝ)‖ :=
      continuous_norm.comp continuous_subtype_val
    have h1 : Continuous fun t : realS S ↦ ‖(t : V → ℝ)‖⁻¹ := h0.inv₀ fun t ↦ by
      obtain ⟨σ, -, hσ⟩ := mem_realS.1 t.2
      exact (norm_pos_of_mem_face hσ).ne'
    exact Continuous.subtype_mk (h1.smul continuous_subtype_val) _
  continuous_invFun := by
    have h0 : Continuous fun u : cubeS S ↦ ∑ v, (u : V → ℝ) v :=
      continuous_finset_sum _ fun v _ ↦ (continuous_apply v).comp continuous_subtype_val
    have h1 : Continuous fun u : cubeS S ↦ (∑ v, (u : V → ℝ) v)⁻¹ :=
      h0.inv₀ fun u ↦ (sum_pos_of_mem_cubeS u.2).ne'
    exact Continuous.subtype_mk (h1.smul continuous_subtype_val) _

end Cube

section Tent

/-- The tent function `max 0 (1 - |x|)`. -/
private def tent (x : ℝ) : ℝ := max 0 (1 - |x|)

private lemma tent_nonneg (x : ℝ) : 0 ≤ tent x := le_max_left _ _

private lemma continuous_tent : Continuous tent :=
  continuous_const.max (continuous_const.sub continuous_abs)

private lemma tent_eq_zero {x : ℝ} (h : 1 ≤ |x|) : tent x = 0 :=
  max_eq_left (by linarith)

/-- The tent functions at the integers `0, …, m` reproduce affine functions on `[0, m]`. -/
private lemma sum_tent_mul (m : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ m) (a b : ℝ) :
    ∑ k : Fin (m + 1), tent (x - k) * (a + b * k) = a + b * x := by
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ tent (x - k) * (a + b * k))]
  set n := ⌊x⌋₊ with hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le h0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hnm : n ≤ m := Nat.floor_le_of_le h1
  have hfar : ∀ c : ℕ, c ≠ n → c ≠ n + 1 → tent (x - c) = 0 := by
    intro c hc hc'
    apply tent_eq_zero
    rcases lt_or_gt_of_ne hc with hlt | hlt
    · have : (c : ℝ) + 1 ≤ n := by exact_mod_cast hlt
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (n : ℝ) + 2 ≤ c := by exact_mod_cast (show n + 2 ≤ c by omega)
      rw [abs_of_neg (by linarith)]; linarith
  have htn : tent (x - n) = 1 - (x - n) := by
    rw [tent, abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  rcases eq_or_lt_of_le hnm with hnm' | hnm'
  · -- `x = m`
    have hx : x = m := le_antisymm h1 (by rw [← hnm']; exact hnx)
    rw [Finset.sum_eq_single n (fun c hcm hc ↦ by
      rw [hfar c hc (by have := Finset.mem_range.1 hcm; omega), zero_mul])
      (fun h ↦ absurd (Finset.mem_range.2 (by omega)) h), htn, hx, ← hnm']
    ring
  · have htn' : tent (x - (n + 1 : ℕ)) = x - n := by
      rw [tent, Nat.cast_add, Nat.cast_one, abs_of_neg (by linarith), max_eq_right (by linarith)]
      ring
    rw [Finset.sum_eq_add n (n + 1) (by omega) (fun c _ hc ↦ by
      rw [hfar c hc.1 hc.2, zero_mul]) (fun h ↦ absurd (Finset.mem_range.2 (by omega)) h)
      (fun h ↦ absurd (Finset.mem_range.2 (by omega)) h), htn, htn']
    push_cast
    ring

private lemma sum_tent (m : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ m) :
    ∑ k : Fin (m + 1), tent (x - k) = 1 := by
  simpa using sum_tent_mul m h0 h1 1 0

/-- An integer is within distance `< 1` of `x` iff it lies between `⌊x⌋` and `⌈x⌉`. -/
private lemma abs_sub_lt_one_iff (x : ℝ) (k : ℤ) :
    |x - k| < 1 ↔ ⌊x⌋ ≤ k ∧ k ≤ ⌈x⌉ := by
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Int.le_of_lt_add_one ?_, Int.le_of_lt_add_one ?_⟩
    · exact_mod_cast (Int.floor_le x).trans_lt (by linarith : x < k + 1)
    · have := Int.le_ceil x
      exact_mod_cast (show (k : ℝ) < ⌈x⌉ + 1 by linarith)
  · rintro ⟨h1, h2⟩
    have hf := Int.floor_le x
    have hf' := Int.lt_floor_add_one x
    have hc := Int.le_ceil x
    have hc' := Int.ceil_lt_add_one x
    have h1' : (⌊x⌋ : ℝ) ≤ k := by exact_mod_cast h1
    have h2' : (k : ℝ) ≤ ⌈x⌉ := by exact_mod_cast h2
    have hcf : (⌈x⌉ : ℝ) ≤ ⌊x⌋ + 1 := by exact_mod_cast Int.ceil_le_floor_add_one x
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h]
      constructor <;> linarith
    · have : (⌊x⌋ : ℝ) + 1 ≤ k := by exact_mod_cast Int.add_one_le_of_lt h
      constructor <;> linarith

end Tent

section Grid

open scoped Classical

variable {V : Type*} [Fintype V] (S : Set (Finset V)) (m : ℕ)

/-- The point of `[0, 1]^V` with coordinates `g / m`. -/
private def gridPt (g : V → Fin (m + 1)) : V → ℝ := fun v ↦ (g v : ℝ) / m

/-- The grid points of mesh `1 / m` in the cubical realization. -/
private abbrev Grid : Type _ := {g : V → Fin (m + 1) // gridPt m g ∈ cubeS S}

/-- The multilinear tent weight of the grid point `g` at `u`. -/
private def wt (u : V → ℝ) (g : V → Fin (m + 1)) : ℝ := ∏ v, tent (m * u v - g v)

/-- The grid points within `1 / m` of `u` in every coordinate. -/
private def nearSet (u : V → ℝ) : Finset (Grid S m) :=
  Finset.univ.filter fun g ↦ ∀ v, |m * u v - (g.1 v : ℝ)| < 1

/-- The simplices of the grid subdivision. -/
private def gridS : Set (Finset (Grid S m)) := {J | ∃ u ∈ cubeS S, J = nearSet S m u}

variable {S m}

private lemma nearSet_mem_gridS {u : V → ℝ} (hu : u ∈ cubeS S) :
    nearSet S m u ∈ gridS S m := ⟨u, hu, rfl⟩

private lemma gridPt_mem {u : V → ℝ} (hm : 0 < m) (hu : u ∈ cubeS S) {g : V → Fin (m + 1)}
    (hg : ∀ v, |m * u v - (g v : ℝ)| < 1) : gridPt m g ∈ cubeS S := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hI, ⟨v₀, hv₀⟩, σ, hσS, hσ⟩ := hu
  refine ⟨fun v ↦ ⟨div_nonneg (Nat.cast_nonneg _) hm'.le, ?_⟩, ⟨v₀, ?_⟩, σ, hσS, fun v hv ↦ ?_⟩
  · rw [gridPt, div_le_one hm']
    exact_mod_cast Nat.lt_succ_iff.1 (g v).2
  · have h := hg v₀
    rw [hv₀, mul_one, abs_lt] at h
    have hgv : (g v₀ : ℕ) ≤ m := Nat.lt_succ_iff.1 (g v₀).2
    have : m ≤ (g v₀ : ℕ) := by
      have : (m : ℝ) - 1 < (g v₀ : ℕ) := by linarith [h.2]
      have : (m : ℤ) - 1 < (g v₀ : ℕ) := by exact_mod_cast this
      omega
    rw [gridPt, show ((g v₀ : ℕ) : ℝ) = m by exact_mod_cast le_antisymm hgv this,
      div_self hm'.ne']
  · have h := hg v
    rw [hσ v hv, mul_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at h
    have h0 : ((g v : ℕ) : ℝ) = 0 := by
      have : (g v : ℕ) < 1 := by exact_mod_cast h
      have : (g v : ℕ) = 0 := by omega
      rw [this, Nat.cast_zero]
    rw [gridPt, h0, zero_div]

private lemma wt_eq_zero {u : V → ℝ} {g : V → Fin (m + 1)}
    (hg : ¬ ∀ v, |m * u v - (g v : ℝ)| < 1) : wt m u g = 0 := by
  push Not at hg
  obtain ⟨v, hv⟩ := hg
  exact Finset.prod_eq_zero (Finset.mem_univ v) (tent_eq_zero hv)

/-- Sums over the grid points in the cubical realization of functions vanishing far from `u`. -/
private lemma sum_grid_eq {u : V → ℝ} (hm : 0 < m) (hu : u ∈ cubeS S)
    (φ : (V → Fin (m + 1)) → ℝ) (hφ : ∀ g, ¬ (∀ v, |m * u v - (g v : ℝ)| < 1) → φ g = 0) :
    ∑ g : Grid S m, φ g.1 = ∑ g : V → Fin (m + 1), φ g := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun g ↦ gridPt m g ∈ cubeS S)
    (fun g ↦ by simp) φ]
  refine Finset.sum_filter_of_ne fun g _ hg ↦ ?_
  by_contra hmem
  exact hg (hφ g fun h ↦ hmem (gridPt_mem hm hu h))

private lemma wt_mem_face {u : V → ℝ} (hm : 0 < m) (hu : u ∈ cubeS S) :
    (fun g : Grid S m ↦ wt m u g.1) ∈ face (nearSet S m u) := by
  refine ⟨fun g ↦ Finset.prod_nonneg fun v _ ↦ tent_nonneg _, ?_, fun g hg ↦ ?_⟩
  · rw [sum_grid_eq hm hu (wt m u) fun g hg ↦ wt_eq_zero hg]
    simp only [wt]
    rw [← Fintype.prod_sum (fun v (k : Fin (m + 1)) ↦ tent (m * u v - k))]
    refine Finset.prod_eq_one fun v _ ↦ sum_tent m (mul_nonneg (Nat.cast_nonneg _) (hu.1 v).1) ?_
    simpa using mul_le_of_le_one_right (Nat.cast_nonneg m) (hu.1 v).2
  · exact wt_eq_zero fun h ↦ hg (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

private lemma wt_mem_realS {u : V → ℝ} (hm : 0 < m) (hu : u ∈ cubeS S) :
    (fun g : Grid S m ↦ wt m u g.1) ∈ realS (gridS S m) :=
  mem_realS.2 ⟨nearSet S m u, nearSet_mem_gridS hu, wt_mem_face hm hu⟩

/-- Barycentric combination of grid points. -/
private def gMap (t : Grid S m → ℝ) : V → ℝ := fun v ↦ ∑ g : Grid S m, t g * gridPt m g.1 v

private lemma gMap_wt {u : V → ℝ} (hm : 0 < m) (hu : u ∈ cubeS S) :
    gMap (fun g : Grid S m ↦ wt m u g.1) = u := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  funext v
  simp only [gMap]
  rw [sum_grid_eq hm hu (fun g ↦ wt m u g * gridPt m g v) fun g hg ↦ by
    rw [wt_eq_zero hg, zero_mul]]
  have key : ∀ g : V → Fin (m + 1), wt m u g * gridPt m g v =
      ∏ v', tent (m * u v' - g v') * (if v' = v then ((g v' : ℕ) : ℝ) / m else 1) := by
    intro g
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ v,
      if_pos (Finset.mem_univ v)]
    rfl
  simp_rw [key]
  rw [← Fintype.prod_sum (fun v' (k : Fin (m + 1)) ↦
    tent (m * u v' - k) * (if v' = v then ((k : ℕ) : ℝ) / m else 1))]
  have h0 : ∀ w, 0 ≤ (m : ℝ) * u w := fun w ↦ mul_nonneg hm'.le (hu.1 w).1
  have h1 : ∀ w, (m : ℝ) * u w ≤ m := fun w ↦ by
    simpa using mul_le_of_le_one_right hm'.le (hu.1 w).2
  rw [Finset.prod_eq_single v (fun v' _ hv' ↦ by
    simp only [if_neg hv', mul_one]; exact sum_tent m (h0 v') (h1 v')) (by simp)]
  simp only [if_pos rfl]
  have := sum_tent_mul m (h0 v) (h1 v) 0 (1 / m)
  simp only [zero_add] at this
  calc ∑ k : Fin (m + 1), tent (m * u v - k) * (((k : ℕ) : ℝ) / m)
      = ∑ k : Fin (m + 1), tent (m * u v - k) * (1 / m * k) :=
        Finset.sum_congr rfl fun k _ ↦ by ring
    _ = u v := by rw [this]; field_simp

private lemma eq_m_of_near {k : ℕ} (hk : k ≤ m) (h : |(m : ℝ) * 1 - k| < 1) : k = m := by
  rw [mul_one, abs_lt] at h
  have : (m : ℝ) - 1 < k := by linarith [h.2]
  have : (m : ℤ) - 1 < k := by exact_mod_cast this
  omega

private lemma eq_zero_of_near {k : ℕ} (h : |(m : ℝ) * 0 - k| < 1) : k = 0 := by
  rw [mul_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at h
  have : k < 1 := by exact_mod_cast h
  omega

private lemma gMap_mem {u : V → ℝ} (hm : 0 < m) (hu : u ∈ cubeS S) {t : Grid S m → ℝ}
    (ht : t ∈ face (nearSet S m u)) : gMap t ∈ cubeS S := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨-, ⟨v₀, hv₀⟩, σ, hσS, hσ⟩ := hu
  have hcoef : ∀ g : Grid S m, t g ≠ 0 → ∀ v, |m * u v - ((g.1 v : ℕ) : ℝ)| < 1 := by
    intro g hg
    by_contra h
    exact hg (ht.2.2 g fun hmem ↦ h (Finset.mem_filter.1 hmem).2)
  refine ⟨fun v ↦ ⟨Finset.sum_nonneg fun g _ ↦ mul_nonneg (ht.1 g) (g.2.1 v).1, ?_⟩,
    ⟨v₀, ?_⟩, σ, hσS, fun v hv ↦ ?_⟩
  · calc gMap t v ≤ ∑ g : Grid S m, t g * 1 :=
          Finset.sum_le_sum fun g _ ↦ mul_le_mul_of_nonneg_left (g.2.1 v).2 (ht.1 g)
      _ = 1 := by simp [ht.2.1]
  · calc gMap t v₀ = ∑ g : Grid S m, t g * 1 := by
          refine Finset.sum_congr rfl fun g _ ↦ ?_
          by_cases hg : t g = 0
          · simp [hg]
          · have := eq_m_of_near (Nat.lt_succ_iff.1 (g.1 v₀).2) (hv₀ ▸ hcoef g hg v₀)
            rw [gridPt, this, div_self hm'.ne']
      _ = 1 := by simp [ht.2.1]
  · refine Finset.sum_eq_zero fun g _ ↦ ?_
    by_cases hg : t g = 0
    · simp [hg]
    · have := eq_zero_of_near (hσ v hv ▸ hcoef g hg v)
      rw [gridPt, this, Nat.cast_zero, zero_div, mul_zero]

private lemma nearSet_gMap_subset {u : V → ℝ} (hm : 0 < m) {t : Grid S m → ℝ}
    (ht : t ∈ face (nearSet S m u)) : nearSet S m (gMap t) ⊆ nearSet S m u := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  intro g hg
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun v ↦ ?_⟩
  have hgv := (Finset.mem_filter.1 hg).2 v
  rw [show ((g.1 v : ℕ) : ℝ) = (((g.1 v : ℕ) : ℤ) : ℝ) by simp] at hgv ⊢
  rw [abs_sub_lt_one_iff] at hgv ⊢
  -- `m * (gMap t v)` is a convex combination of grid values near `m * u v`
  have hy : (m : ℝ) * gMap t v = ∑ g' : Grid S m, t g' * ((g'.1 v : ℕ) : ℝ) := by
    simp only [gMap, Finset.mul_sum, gridPt]
    refine Finset.sum_congr rfl fun g' _ ↦ ?_
    field_simp
  have hnear : ∀ g' : Grid S m, t g' ≠ 0 →
      ⌊(m : ℝ) * u v⌋ ≤ ((g'.1 v : ℕ) : ℤ) ∧ ((g'.1 v : ℕ) : ℤ) ≤ ⌈(m : ℝ) * u v⌉ := by
    intro g' hg'
    have h : |(m : ℝ) * u v - ((g'.1 v : ℕ) : ℝ)| < 1 := by
      by_contra h
      exact hg' (ht.2.2 g' fun hmem ↦ h ((Finset.mem_filter.1 hmem).2 v))
    rw [show ((g'.1 v : ℕ) : ℝ) = (((g'.1 v : ℕ) : ℤ) : ℝ) by simp, abs_sub_lt_one_iff] at h
    exact h
  have hlo : (⌊(m : ℝ) * u v⌋ : ℝ) ≤ (m : ℝ) * gMap t v := by
    rw [hy]
    calc (⌊(m : ℝ) * u v⌋ : ℝ) = ∑ g' : Grid S m, t g' * ⌊(m : ℝ) * u v⌋ := by
          rw [← Finset.sum_mul, ht.2.1, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun g' _ ↦ by
          by_cases hg' : t g' = 0
          · simp [hg']
          · exact mul_le_mul_of_nonneg_left (by exact_mod_cast (hnear g' hg').1) (ht.1 g')
  have hhi : (m : ℝ) * gMap t v ≤ (⌈(m : ℝ) * u v⌉ : ℝ) := by
    rw [hy]
    calc _ ≤ ∑ g' : Grid S m, t g' * ⌈(m : ℝ) * u v⌉ := Finset.sum_le_sum fun g' _ ↦ by
          by_cases hg' : t g' = 0
          · simp [hg']
          · exact mul_le_mul_of_nonneg_left (by exact_mod_cast (hnear g' hg').2) (ht.1 g')
      _ = _ := by rw [← Finset.sum_mul, ht.2.1, one_mul]
  exact ⟨(Int.le_floor.2 hlo).trans hgv.1, hgv.2.trans (Int.ceil_le.2 hhi)⟩

variable (S) in
/-- **Subdivision**: the cubical realization is homotopy equivalent to the realization of its
grid subdivision of mesh `1 / m`, by the multilinear tent weights. -/
private lemma exists_homotopyEquiv_gridS (hm : 0 < m) :
    ∃ e : ContinuousMap.HomotopyEquiv (cubeS S) (realS (gridS S m)),
      ∀ u, (e.toFun u : Grid S m → ℝ) = fun g ↦ wt m u g.1 := by
  have hwc : Continuous fun u : cubeS S ↦ fun g : Grid S m ↦ wt m (u : V → ℝ) g.1 :=
    continuous_pi fun g ↦ continuous_finset_prod _ fun v _ ↦ continuous_tent.comp
      ((continuous_const.mul ((continuous_apply v).comp continuous_subtype_val)).sub
        continuous_const)
  have hmem : ∀ u : cubeS S, (fun g : Grid S m ↦ wt m (u : V → ℝ) g.1) ∈ realS (gridS S m) :=
    fun u ↦ wt_mem_realS (S := S) (m := m) hm u.2
  let toF : C(cubeS S, realS (gridS S m)) :=
    { toFun := fun u ↦ ⟨fun g : Grid S m ↦ wt m (u : V → ℝ) g.1, hmem u⟩
      continuous_toFun := hwc.subtype_mk hmem }
  have hgc : Continuous (gMap (S := S) (m := m)) :=
    continuous_pi fun v ↦ continuous_finset_sum _ fun g _ ↦
      (continuous_apply g).mul continuous_const
  have hgmem : ∀ t : realS (gridS S m), gMap (S := S) (m := m) t ∈ cubeS S := by
    intro t
    obtain ⟨J, ⟨u, hu, rfl⟩, ht⟩ := mem_realS.1 t.2
    exact gMap_mem (S := S) (m := m) hm hu ht
  let invF : C(realS (gridS S m), cubeS S) :=
    { toFun := fun t ↦ ⟨gMap (S := S) (m := m) t, hgmem t⟩
      continuous_toFun := (hgc.comp continuous_subtype_val).subtype_mk hgmem }
  have hleft : invF.comp toF = ContinuousMap.id _ := by
    ext u : 2
    exact gMap_wt (S := S) (m := m) hm u.2
  have hface : ∀ t : realS (gridS S m), ∃ u ∈ cubeS S,
      (toF (invF t) : Grid S m → ℝ) ∈ face (nearSet S m u) ∧
        (t : Grid S m → ℝ) ∈ face (nearSet S m u) := by
    intro t
    obtain ⟨J, ⟨u, hu, rfl⟩, ht⟩ := mem_realS.1 t.2
    exact ⟨u, hu, face_mono (nearSet_gMap_subset (S := S) (m := m) hm ht)
      (wt_mem_face (S := S) (m := m) hm (gMap_mem (S := S) (m := m) hm hu ht)), ht⟩
  have hHmem : ∀ p : unitInterval × realS (gridS S m),
      (1 - (p.1 : ℝ)) • (toF (invF p.2) : Grid S m → ℝ) + (p.1 : ℝ) • (p.2 : Grid S m → ℝ) ∈
        realS (gridS S m) := by
    intro p
    obtain ⟨u, hu, h1, h2⟩ := hface p.2
    exact mem_realS.2 ⟨_, nearSet_mem_gridS (S := S) (m := m) hu,
      convex_face _ h1 h2 (by linarith [p.1.2.2]) p.1.2.1 (by ring)⟩
  have hHc : Continuous fun p : unitInterval × realS (gridS S m) ↦
      (1 - (p.1 : ℝ)) • (toF (invF p.2) : Grid S m → ℝ) + (p.1 : ℝ) • (p.2 : Grid S m → ℝ) := by
    have hs : Continuous fun p : unitInterval × realS (gridS S m) ↦ ((p.1 : unitInterval) : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub hs).smul (continuous_subtype_val.comp
      ((toF.comp invF).continuous.comp continuous_snd))).add
      (hs.smul (continuous_subtype_val.comp continuous_snd))
  have hright : (toF.comp invF).Homotopic (ContinuousMap.id _) :=
    ⟨⟨⟨fun p ↦ ⟨_, hHmem p⟩, hHc.subtype_mk hHmem⟩, fun t ↦ by ext; simp,
      fun t ↦ by ext; simp⟩⟩
  exact ⟨⟨toF, invF, by rw [hleft], hright⟩, fun u ↦ rfl⟩

end Grid

section Geometric

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The space of a finite geometric simplicial complex is homeomorphic to the abstract
realization of its family of faces (barycentric coordinates). -/
private lemma exists_realS_homeomorph_space (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) :
    ∃ (V : Type u) (_ : Fintype V) (S : Set (Finset V)), S.Finite ∧
      Nonempty (K.space ≃ₜ realS S) := by
  classical
  let P : Set E := ⋃ s ∈ K.faces, (s : Set E)
  have hP : P.Finite := hK.biUnion fun s _ ↦ s.finite_toSet
  letI : Fintype P := hP.fintype
  let emb : Finset P → Finset E := fun σ ↦ σ.map (Function.Embedding.subtype _)
  have hemb : Function.Injective emb := Finset.map_injective _
  let S : Set (Finset P) := emb ⁻¹' K.faces
  have hS : S.Finite := hK.preimage hemb.injOn
  let T : (P → ℝ) → E := fun t ↦ ∑ v, t v • (v : E)
  have hT : Continuous T := continuous_finset_sum _ fun v _ ↦
    (continuous_apply v).smul continuous_const
  have hTσ : ∀ σ : Finset P, ∀ t ∈ face σ, T t = ∑ v ∈ σ, t v • (v : E) := fun σ t ht ↦
    (Finset.sum_subset (Finset.subset_univ σ) fun v _ hv ↦ by simp [ht.2.2 v hv]).symm
  -- barycentric coordinates map faces into the convex hulls
  have h1 : ∀ σ : Finset P, ∀ t ∈ face σ, T t ∈ convexHull ℝ (emb σ : Set E) := by
    intro σ t ht
    rw [hTσ σ t ht]
    refine (convex_convexHull ℝ _).sum_mem (fun v _ ↦ ht.1 v) ?_ fun v hv ↦
      subset_convexHull ℝ _ (Finset.mem_map_of_mem _ hv)
    rw [← ht.2.1]
    exact Finset.sum_subset (Finset.subset_univ σ) fun v _ hv ↦ ht.2.2 v hv
  -- every point of a convex hull has barycentric coordinates
  have h2 : ∀ σ : Finset P, ∀ x ∈ convexHull ℝ (emb σ : Set E), ∃ t ∈ face σ, T t = x := by
    intro σ x hx
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hx
    let t : P → ℝ := fun v ↦ if v ∈ σ then w v else 0
    have ht : t ∈ face σ := by
      refine ⟨fun v ↦ ?_, ?_, fun v hv ↦ if_neg hv⟩
      · show 0 ≤ (if v ∈ σ then w v else 0)
        split_ifs with h
        · exact hw0 _ (Finset.mem_map_of_mem _ h)
        · exact le_rfl
      · rw [← Finset.sum_subset (Finset.subset_univ σ) fun v _ hv ↦ if_neg hv,
          Finset.sum_congr rfl fun v hv ↦ if_pos hv, ← hw1]
        exact (Finset.sum_map σ (Function.Embedding.subtype _) w).symm
    refine ⟨t, ht, ?_⟩
    rw [hTσ σ t ht, Finset.sum_congr rfl fun v hv ↦ by rw [show t v = w v from if_pos hv], ← hwx]
    exact (Finset.sum_map σ (Function.Embedding.subtype _) fun y ↦ w y • y).symm
  -- uniqueness of barycentric coordinates on a face
  have hU : ∀ σ ∈ S, ∀ t ∈ face σ, ∀ t' ∈ face σ, T t = T t' → t = t' := by
    intro σ hσ t ht t' ht' htt'
    have hind := K.indep hσ
    let f : σ ↪ ((emb σ : Finset E) : Set E) :=
      ⟨fun v ↦ ⟨(v : P), Finset.mem_map_of_mem _ v.2⟩, fun a b h ↦ by
        have h' := congrArg (fun z : ((emb σ : Finset E) : Set E) ↦ (z : E)) h
        exact Subtype.ext (Subtype.ext h')⟩
    have hind' : AffineIndependent ℝ (fun v : σ ↦ ((v : P) : E)) := hind.comp_embedding f
    have hsum : ∀ u ∈ face σ, ∑ v : σ, u v = 1 := fun u hu ↦ by
      rw [← hu.2.1, Finset.sum_coe_sort σ u]
      exact Finset.sum_subset (Finset.subset_univ σ) fun v _ hv ↦ hu.2.2 v hv
    have hcomb : ∀ u ∈ face σ, Finset.univ.affineCombination ℝ (fun v : σ ↦ ((v : P) : E))
        (fun v ↦ u v) = T u := fun u hu ↦ by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (hsum u hu), hTσ σ u hu]
      exact Finset.sum_coe_sort σ fun v ↦ u v • (v : E)
    have := (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ _).1 hind'
      (fun v ↦ t v) (fun v ↦ t' v) (hsum t ht) (hsum t' ht')
      (by rw [hcomb t ht, hcomb t' ht', htt'])
    funext v
    by_cases hv : v ∈ σ
    · exact congrFun this ⟨v, hv⟩
    · rw [ht.2.2 v hv, ht'.2.2 v hv]
  have hinj : Set.InjOn T (realS S) := by
    intro t ht t' ht' htt'
    obtain ⟨σ, hσ, htσ⟩ := mem_realS.1 ht
    obtain ⟨σ', hσ', htσ'⟩ := mem_realS.1 ht'
    have hx : T t ∈ convexHull ℝ (emb (σ ∩ σ') : Set E) := by
      have := K.inter_subset_convexHull hσ hσ' ⟨h1 σ t htσ, htt' ▸ h1 σ' t' htσ'⟩
      refine convexHull_mono ?_ this
      intro y ⟨hy, hy'⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hy
      obtain ⟨v', hv', hvv'⟩ := Finset.mem_map.1 hy'
      obtain rfl : v' = v := Subtype.ext hvv'
      exact Finset.mem_map_of_mem _ (Finset.mem_inter.2 ⟨hv, hv'⟩)
    obtain ⟨t'', ht'', hT''⟩ := h2 _ _ hx
    have e1 := hU σ hσ t htσ t'' (face_mono Finset.inter_subset_left ht'') hT''.symm
    have e2 := hU σ' hσ' t' htσ' t'' (face_mono Finset.inter_subset_right ht'')
      (by rw [hT'', htt'])
    rw [e1, e2]
  have hmem : ∀ t ∈ realS S, T t ∈ K.space := by
    intro t ht
    obtain ⟨σ, hσ, htσ⟩ := mem_realS.1 ht
    exact Geometry.SimplicialComplex.mem_space_iff.2 ⟨_, hσ, h1 σ t htσ⟩
  have hsurj : ∀ x ∈ K.space, ∃ t ∈ realS S, T t = x := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.1 hx
    let σ : Finset P := Finset.univ.filter fun v ↦ (v : E) ∈ s
    have hσ : emb σ = s := by
      ext y
      simp only [emb, σ, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coe_subtype]
      exact ⟨fun ⟨_, hv, h⟩ ↦ h ▸ hv, fun hy ↦ ⟨⟨y, Set.mem_biUnion hs hy⟩, hy, rfl⟩⟩
    obtain ⟨t, ht, rfl⟩ := h2 σ x (by rwa [hσ])
    exact ⟨t, mem_realS.2 ⟨σ, show emb σ ∈ K.faces by rwa [hσ], ht⟩, rfl⟩
  haveI : CompactSpace (realS S) := isCompact_iff_compactSpace.1 (isCompact_realS hS)
  let e : realS S ≃ K.space := Equiv.ofBijective (fun t ↦ ⟨T t, hmem t t.2⟩)
    ⟨fun a b h ↦ Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val h)), fun x ↦ by
      obtain ⟨t, ht, htx⟩ := hsurj x x.2
      exact ⟨⟨t, ht⟩, Subtype.ext htx⟩⟩
  have he : Continuous e := Continuous.subtype_mk (hT.comp continuous_subtype_val) _
  exact ⟨P, inferInstance, S, hS, ⟨(he.homeoOfEquivCompactToT2).symm⟩⟩

end Geometric

end

end RealPart

section Approx

open scoped Classical

noncomputable section

variable {W V : Type*} [Fintype W] [Fintype V]

/-- Push-forward of weights along a map of vertices. -/
private def pushV (β : W → V) (t : W → ℝ) : V → ℝ := fun a ↦ ∑ w, if β w = a then t w else 0

private lemma continuous_pushV (β : W → V) : Continuous (pushV β) :=
  continuous_pi fun a ↦ continuous_finset_sum _ fun w _ ↦
    continuous_if_const _ (fun _ ↦ continuous_apply w) fun _ ↦ continuous_const

private lemma sum_pushV (β : W → V) (t : W → ℝ) : ∑ a, pushV β t a = ∑ w, t w := by
  simp only [pushV]
  rw [Finset.sum_comm]
  simp

private lemma pushV_mem_face {β : W → V} {J : Finset W} {t : W → ℝ} (ht : t ∈ face J) :
    pushV β t ∈ face (J.image β) := by
  refine ⟨fun a ↦ Finset.sum_nonneg fun w _ ↦ ?_, by rw [sum_pushV, ht.2.1], fun a ha ↦ ?_⟩
  · split_ifs
    · exact ht.1 w
    · exact le_rfl
  · refine Finset.sum_eq_zero fun w _ ↦ ?_
    split_ifs with h
    · exact ht.2.2 w fun hw ↦ ha (Finset.mem_image.2 ⟨w, hw, h⟩)
    · rfl

private lemma pushV_add_smul (β : W → V) (a b : ℝ) (t t' : W → ℝ) :
    pushV β (a • t + b • t') = a • pushV β t + b • pushV β t' := by
  funext x
  simp only [pushV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  split_ifs <;> ring

private lemma pushV_smul (β : W → V) (a : ℝ) (t : W → ℝ) : pushV β (a • t) = a • pushV β t := by
  simpa using pushV_add_smul β a 0 t 0

private lemma pushV_mem_realS {S₀ : Set (Finset W)} {S₁ : Set (Finset V)} {β : W → V}
    (hβ : ∀ J ∈ S₀, ∃ τ ∈ S₁, J.image β ⊆ τ) {t : W → ℝ} (ht : t ∈ realS S₀) :
    pushV β t ∈ realS S₁ := by
  obtain ⟨J, hJ, ht⟩ := mem_realS.1 ht
  obtain ⟨τ, hτ, hJτ⟩ := hβ J hJ
  exact mem_realS.2 ⟨τ, hτ, face_mono hJτ (pushV_mem_face ht)⟩

/-- The push-forward along a simplicial vertex map, on realizations. -/
private def pushR {S₀ : Set (Finset W)} {S₁ : Set (Finset V)} (β : W → V)
    (hβ : ∀ J ∈ S₀, ∃ τ ∈ S₁, J.image β ⊆ τ) : C(realS S₀, realS S₁) where
  toFun t := ⟨pushV β t, pushV_mem_realS hβ t.2⟩
  continuous_toFun := ((continuous_pushV β).comp continuous_subtype_val).subtype_mk _

@[local simp] private lemma coe_pushR {S₀ : Set (Finset W)} {S₁ : Set (Finset V)} {β : W → V}
    {hβ : ∀ J ∈ S₀, ∃ τ ∈ S₁, J.image β ⊆ τ} (t : realS S₀) :
    (pushR β hβ t : V → ℝ) = pushV β t := rfl

private lemma isCompact_cubeS {S : Set (Finset V)} (hS : S.Finite) : IsCompact (cubeS S) := by
  haveI : CompactSpace (realS S) := isCompact_iff_compactSpace.1 (isCompact_realS hS)
  exact isCompact_iff_compactSpace.2 (realSHomeoCubeS S).compactSpace

/-- **Simplicial approximation** on the cubical realization: for a fine enough grid
subdivision, every grid vertex `g` can be sent to vertices `β g`, `γ g` whose open stars contain
the images of the star of `g`, and the resulting simplicial maps are carried by the same
simplices as `F` and `G`. -/
private lemma exists_simplicialApprox {V₀ V₁ V₂ : Type*} [Fintype V₀] [Fintype V₁]
    [Fintype V₂] {S₀ : Set (Finset V₀)} (hS₀ : S₀.Finite) {S₁ : Set (Finset V₁)}
    {S₂ : Set (Finset V₂)} (F : C(cubeS S₀, realS S₁)) (G : C(cubeS S₀, realS S₂)) :
    ∃ (m : ℕ) (_ : 0 < m) (β : Grid S₀ m → V₁) (γ : Grid S₀ m → V₂),
      (∀ J ∈ gridS S₀ m, ∃ τ ∈ S₁, J.image β ⊆ τ) ∧
      (∀ J ∈ gridS S₀ m, ∃ τ ∈ S₂, J.image γ ⊆ τ) ∧
      (∀ u : cubeS S₀, ∃ τ ∈ S₁, (F u : V₁ → ℝ) ∈ face τ ∧
        pushV β (fun g : Grid S₀ m ↦ wt m u g.1) ∈ face τ) ∧
      (∀ u : cubeS S₀, ∃ τ ∈ S₂, (G u : V₂ → ℝ) ∈ face τ ∧
        pushV γ (fun g : Grid S₀ m ↦ wt m u g.1) ∈ face τ) := by
  -- the open cover by preimages of pairs of open stars
  have hWo : ∀ k : V₁ × V₂, IsOpen {u : cubeS S₀ | 0 < (F u : V₁ → ℝ) k.1 ∧
      0 < (G u : V₂ → ℝ) k.2} := fun k ↦
    (isOpen_lt continuous_const ((continuous_apply k.1).comp
      (continuous_subtype_val.comp F.continuous))).inter
    (isOpen_lt continuous_const ((continuous_apply k.2).comp
      (continuous_subtype_val.comp G.continuous)))
  choose O hO hOeq using fun k ↦ isOpen_induced_iff.1 (hWo k)
  have hcov : cubeS S₀ ⊆ ⋃ k, O k := by
    intro u hu
    obtain ⟨τ, -, hτ⟩ := mem_realS.1 (F ⟨u, hu⟩).2
    obtain ⟨a, -, ha⟩ := exists_pos_of_mem_face hτ
    obtain ⟨τ', -, hτ'⟩ := mem_realS.1 (G ⟨u, hu⟩).2
    obtain ⟨b, -, hb⟩ := exists_pos_of_mem_face hτ'
    have : (⟨u, hu⟩ : cubeS S₀) ∈ Subtype.val ⁻¹' O (a, b) := by
      rw [hOeq]; exact ⟨ha, hb⟩
    exact Set.mem_iUnion.2 ⟨(a, b), this⟩
  obtain ⟨δ, hδ, hδO⟩ := lebesgue_number_lemma_of_metric (isCompact_cubeS hS₀) hO hcov
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set m := n + 1 with hm_def
  have hm : 0 < m := Nat.succ_pos n
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmδ : 1 / (m : ℝ) < δ := by simpa [hm_def] using hn
  choose k hk using fun g : Grid S₀ m ↦ hδO (gridPt m g.1) g.2
  -- points near a grid vertex lie in the chosen member of the cover
  have hnear : ∀ (u : cubeS S₀) (g : Grid S₀ m), g ∈ nearSet S₀ m (u : V₀ → ℝ) →
      0 < (F u : V₁ → ℝ) (k g).1 ∧ 0 < (G u : V₂ → ℝ) (k g).2 := by
    intro u g hg
    have hball : (u : V₀ → ℝ) ∈ Metric.ball (gridPt m g.1) δ := by
      rw [Metric.mem_ball, dist_pi_lt_iff hδ]
      intro v
      have h := (Finset.mem_filter.1 hg).2 v
      rw [Real.dist_eq, gridPt]
      calc |(u : V₀ → ℝ) v - ((g.1 v : ℕ) : ℝ) / m|
          = |(m : ℝ) * (u : V₀ → ℝ) v - ((g.1 v : ℕ) : ℝ)| / m := by
            rw [← abs_of_pos hm', ← abs_div, abs_of_pos hm']; congr 1; field_simp
        _ < 1 / m := div_lt_div_of_pos_right h hm'
        _ < δ := hmδ
    have : u ∈ Subtype.val ⁻¹' O (k g) := hk g hball
    rw [hOeq] at this
    exact this
  refine ⟨m, hm, fun g ↦ (k g).1, fun g ↦ (k g).2, ?_, ?_, ?_, ?_⟩
  · rintro J ⟨u, hu, rfl⟩
    obtain ⟨τ, hτS, hτ⟩ := mem_realS.1 (F ⟨u, hu⟩).2
    refine ⟨τ, hτS, fun a ha ↦ ?_⟩
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 ha
    by_contra h
    have := (hnear ⟨u, hu⟩ g hg).1
    rw [hτ.2.2 _ h] at this
    exact lt_irrefl _ this
  · rintro J ⟨u, hu, rfl⟩
    obtain ⟨τ, hτS, hτ⟩ := mem_realS.1 (G ⟨u, hu⟩).2
    refine ⟨τ, hτS, fun a ha ↦ ?_⟩
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 ha
    by_contra h
    have := (hnear ⟨u, hu⟩ g hg).2
    rw [hτ.2.2 _ h] at this
    exact lt_irrefl _ this
  · intro u
    obtain ⟨τ, hτS, hτ⟩ := mem_realS.1 (F u).2
    refine ⟨τ, hτS, hτ, face_mono (fun a ha ↦ ?_) (pushV_mem_face (wt_mem_face hm u.2))⟩
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 ha
    by_contra h
    have := (hnear u g hg).1
    rw [hτ.2.2 _ h] at this
    exact lt_irrefl _ this
  · intro u
    obtain ⟨τ, hτS, hτ⟩ := mem_realS.1 (G u).2
    refine ⟨τ, hτS, hτ, face_mono (fun a ha ↦ ?_) (pushV_mem_face (wt_mem_face hm u.2))⟩
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 ha
    by_contra h
    have := (hnear u g hg).2
    rw [hτ.2.2 _ h] at this
    exact lt_irrefl _ this

end

end Approx

section Join

attribute [local simp] coe_pushR

open scoped Classical

noncomputable section

open DMC

variable {V₀ V₁ V₂ : Type*} [Fintype V₀] [Fintype V₁] [Fintype V₂]

/-- A point of `ℝ^(V₁ ⊕ V₀ ⊕ V₂)` from its three blocks of coordinates. -/
private def mk3 (u : V₁ → ℝ) (v : V₀ → ℝ) (w : V₂ → ℝ) : V₁ ⊕ V₀ ⊕ V₂ → ℝ :=
  Sum.elim u (Sum.elim v w)

private def pu (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) : V₁ → ℝ := fun a ↦ z (.inl a)
private def pv (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) : V₀ → ℝ := fun c ↦ z (.inr (.inl c))
private def pw (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) : V₂ → ℝ := fun b ↦ z (.inr (.inr b))

@[local simp]
private lemma pu_mk3 (u : V₁ → ℝ) (v : V₀ → ℝ) (w : V₂ → ℝ) : pu (mk3 u v w) = u := rfl
@[local simp]
private lemma pv_mk3 (u : V₁ → ℝ) (v : V₀ → ℝ) (w : V₂ → ℝ) : pv (mk3 u v w) = v := rfl
@[local simp]
private lemma pw_mk3 (u : V₁ → ℝ) (v : V₀ → ℝ) (w : V₂ → ℝ) : pw (mk3 u v w) = w := rfl

private lemma continuous_mk3 {X : Type*} [TopologicalSpace X] {u : X → V₁ → ℝ}
    {v : X → V₀ → ℝ} {w : X → V₂ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) : Continuous fun x ↦ mk3 (u x) (v x) (w x) := by
  refine continuous_pi fun y ↦ ?_
  rcases y with a | c | b
  · exact (continuous_apply a).comp hu
  · exact (continuous_apply c).comp hv
  · exact (continuous_apply b).comp hw

private lemma continuous_pu : Continuous (pu (V₀ := V₀) (V₁ := V₁) (V₂ := V₂)) :=
  continuous_pi fun a ↦ continuous_apply _
private lemma continuous_pv : Continuous (pv (V₀ := V₀) (V₁ := V₁) (V₂ := V₂)) :=
  continuous_pi fun a ↦ continuous_apply _
private lemma continuous_pw : Continuous (pw (V₀ := V₀) (V₁ := V₁) (V₂ := V₂)) :=
  continuous_pi fun a ↦ continuous_apply _

private lemma sum_eq_pu_pv_pw (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) :
    ∑ x, z x = ∑ a, pu z a + ∑ c, pv z c + ∑ b, pw z b := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
  rfl

/-- The simplices `τ * σ` of the left half of the join model. -/
private def joinL (σ : Finset V₀) (τ : Finset V₁) : Finset (V₁ ⊕ V₀ ⊕ V₂) :=
  τ.image Sum.inl ∪ σ.image (Sum.inr ∘ Sum.inl)

/-- The simplices `σ * τ` of the right half of the join model. -/
private def joinR (σ : Finset V₀) (τ : Finset V₂) : Finset (V₁ ⊕ V₀ ⊕ V₂) :=
  σ.image (Sum.inr ∘ Sum.inl) ∪ τ.image (Sum.inr ∘ Sum.inr)

variable (S₀ : Set (Finset V₀)) (S₁ : Set (Finset V₁)) (S₂ : Set (Finset V₂))
  (β : V₀ → V₁) (γ : V₀ → V₂)

/-- The simplicial double mapping cylinder of simplicial maps `β`, `γ`: joins of each simplex
with (a simplex containing) its images. -/
private def joinS : Set (Finset (V₁ ⊕ V₀ ⊕ V₂)) :=
  {J | (∃ σ ∈ S₀, ∃ τ ∈ S₁, σ.image β ⊆ τ ∧ J = joinL σ τ) ∨ (∃ τ ∈ S₁, J = τ.image Sum.inl) ∨
    (∃ σ ∈ S₀, ∃ τ ∈ S₂, σ.image γ ⊆ τ ∧ J = joinR σ τ) ∨
    (∃ τ ∈ S₂, J = τ.image (Sum.inr ∘ Sum.inr))}

variable {S₀ S₁ S₂ β γ}

private lemma inl_mem_joinL {σ : Finset V₀} {τ : Finset V₁} {a : V₁} :
    (Sum.inl a : V₁ ⊕ V₀ ⊕ V₂) ∈ joinL σ τ ↔ a ∈ τ := by
  simp only [joinL, Finset.mem_union, Finset.mem_image, Sum.inl.injEq, exists_eq_right,
    Function.comp_apply, reduceCtorEq, and_false, exists_false, or_false]

private lemma inm_mem_joinL {σ : Finset V₀} {τ : Finset V₁} {c : V₀} :
    (Sum.inr (Sum.inl c) : V₁ ⊕ V₀ ⊕ V₂) ∈ joinL σ τ ↔ c ∈ σ := by
  simp only [joinL, Finset.mem_union, Finset.mem_image, Sum.inr.injEq, Sum.inl.injEq,
    exists_eq_right, Function.comp_apply, reduceCtorEq, and_false, exists_false, false_or]

private lemma inr_notMem_joinL {σ : Finset V₀} {τ : Finset V₁} {b : V₂} :
    (Sum.inr (Sum.inr b) : V₁ ⊕ V₀ ⊕ V₂) ∉ joinL σ τ := by
  simp only [joinL, Finset.mem_union, Finset.mem_image, Sum.inr.injEq, Function.comp_apply,
    reduceCtorEq, and_false, exists_false, or_self, not_false_eq_true]

private lemma inr_mem_joinR {σ : Finset V₀} {τ : Finset V₂} {b : V₂} :
    (Sum.inr (Sum.inr b) : V₁ ⊕ V₀ ⊕ V₂) ∈ joinR σ τ ↔ b ∈ τ := by
  simp only [joinR, Finset.mem_union, Finset.mem_image, Sum.inr.injEq, exists_eq_right,
    Function.comp_apply, reduceCtorEq, and_false, exists_false, false_or]

private lemma inm_mem_joinR {σ : Finset V₀} {τ : Finset V₂} {c : V₀} :
    (Sum.inr (Sum.inl c) : V₁ ⊕ V₀ ⊕ V₂) ∈ joinR σ τ ↔ c ∈ σ := by
  simp only [joinR, Finset.mem_union, Finset.mem_image, Sum.inr.injEq, Sum.inl.injEq,
    exists_eq_right, Function.comp_apply, reduceCtorEq, and_false, exists_false, or_false]

private lemma inl_notMem_joinR {σ : Finset V₀} {τ : Finset V₂} {a : V₁} :
    (Sum.inl a : V₁ ⊕ V₀ ⊕ V₂) ∉ joinR σ τ := by
  simp only [joinR, Finset.mem_union, Finset.mem_image, Function.comp_apply, reduceCtorEq,
    and_false, exists_false, or_self, not_false_eq_true]

private lemma mem_face_joinL {σ : Finset V₀} {τ : Finset V₁} {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ} :
    z ∈ face (joinL σ τ) ↔ (∀ x, 0 ≤ z x) ∧ ∑ a, pu z a + ∑ c, pv z c = 1 ∧
      (∀ a ∉ τ, pu z a = 0) ∧ (∀ c ∉ σ, pv z c = 0) ∧ pw z = 0 := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have hw : pw z = 0 := funext fun b ↦ h2 _ inr_notMem_joinL
    refine ⟨h0, ?_, fun a ha ↦ h2 _ (inl_mem_joinL.not.2 ha),
      fun c hc ↦ h2 _ (inm_mem_joinL.not.2 hc), hw⟩
    rw [sum_eq_pu_pv_pw, hw] at h1
    simpa using h1
  · rintro ⟨h0, h1, ha, hc, hw⟩
    refine ⟨h0, by rw [sum_eq_pu_pv_pw, hw]; simpa using h1, fun x hx ↦ ?_⟩
    rcases x with a | c | b
    · exact ha a fun h ↦ hx (inl_mem_joinL.2 h)
    · exact hc c fun h ↦ hx (inm_mem_joinL.2 h)
    · exact congrFun hw b

private lemma mem_face_joinR {σ : Finset V₀} {τ : Finset V₂} {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ} :
    z ∈ face (joinR σ τ) ↔ (∀ x, 0 ≤ z x) ∧ ∑ c, pv z c + ∑ b, pw z b = 1 ∧
      (∀ b ∉ τ, pw z b = 0) ∧ (∀ c ∉ σ, pv z c = 0) ∧ pu z = 0 := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have hu : pu z = 0 := funext fun a ↦ h2 _ inl_notMem_joinR
    refine ⟨h0, ?_, fun b hb ↦ h2 _ (inr_mem_joinR.not.2 hb),
      fun c hc ↦ h2 _ (inm_mem_joinR.not.2 hc), hu⟩
    rw [sum_eq_pu_pv_pw, hu] at h1
    simpa using h1
  · rintro ⟨h0, h1, hb, hc, hu⟩
    refine ⟨h0, by rw [sum_eq_pu_pv_pw, hu]; simpa [add_assoc] using h1, fun x hx ↦ ?_⟩
    rcases x with a | c | b
    · exact congrFun hu a
    · exact hc c fun h ↦ hx (inm_mem_joinR.2 h)
    · exact hb b fun h ↦ hx (inr_mem_joinR.2 h)

private lemma joinL_empty (τ : Finset V₁) :
    joinL (∅ : Finset V₀) τ = (τ.image Sum.inl : Finset (V₁ ⊕ V₀ ⊕ V₂)) := by
  simp only [joinL, Finset.image_empty, Finset.union_empty]

private lemma joinR_empty (τ : Finset V₂) :
    joinR (∅ : Finset V₀) τ = (τ.image (Sum.inr ∘ Sum.inr) : Finset (V₁ ⊕ V₀ ⊕ V₂)) := by
  simp only [joinR, Finset.image_empty, Finset.empty_union]

private lemma pushV_eq_zero {W V : Type*} [Fintype W] [Fintype V] {β : W → V} {J : Finset W}
    {t : W → ℝ} (ht : ∀ w ∉ J, t w = 0) {a : V} (ha : a ∉ J.image β) : pushV β t a = 0 :=
  Finset.sum_eq_zero fun w _ ↦ by
    split_ifs with h
    · exact ht w fun hw ↦ ha (Finset.mem_image.2 ⟨w, hw, h⟩)
    · rfl

private lemma pushV_nonneg {W V : Type*} [Fintype W] [Fintype V] {β : W → V} {t : W → ℝ}
    (ht : ∀ w, 0 ≤ t w) (a : V) : 0 ≤ pushV β t a :=
  Finset.sum_nonneg fun w _ ↦ by split_ifs; exacts [ht w, le_rfl]

/-- The total weights of the three blocks. -/
private def sA (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) : ℝ := ∑ a, pu z a
private def sM (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) : ℝ := ∑ c, pv z c
private def sB (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) : ℝ := ∑ b, pw z b

private lemma continuous_sA : Continuous (sA (V₀ := V₀) (V₁ := V₁) (V₂ := V₂)) :=
  continuous_finset_sum _ fun a _ ↦ (continuous_apply a).comp continuous_pu
private lemma continuous_sM : Continuous (sM (V₀ := V₀) (V₁ := V₁) (V₂ := V₂)) :=
  continuous_finset_sum _ fun a _ ↦ (continuous_apply a).comp continuous_pv
private lemma continuous_sB : Continuous (sB (V₀ := V₀) (V₁ := V₁) (V₂ := V₂)) :=
  continuous_finset_sum _ fun a _ ↦ (continuous_apply a).comp continuous_pw

/-- Points of the join model lie in a left piece `τ * σ` (with `σ` possibly empty) or a right
piece. -/
private lemma mem_realS_joinS {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ} (hz : z ∈ realS (joinS S₀ S₁ S₂ β γ)) :
    (∃ σ : Finset V₀, (σ ∈ S₀ ∨ σ = ∅) ∧ ∃ τ ∈ S₁, σ.image β ⊆ τ ∧ z ∈ face (joinL σ τ)) ∨
    (∃ σ : Finset V₀, (σ ∈ S₀ ∨ σ = ∅) ∧ ∃ τ ∈ S₂, σ.image γ ⊆ τ ∧ z ∈ face (joinR σ τ)) := by
  obtain ⟨J, hJ, hz⟩ := mem_realS.1 hz
  rcases hJ with ⟨σ, hσ, τ, hτ, hστ, rfl⟩ | ⟨τ, hτ, rfl⟩ | ⟨σ, hσ, τ, hτ, hστ, rfl⟩ |
    ⟨τ, hτ, rfl⟩
  · exact Or.inl ⟨σ, Or.inl hσ, τ, hτ, hστ, hz⟩
  · exact Or.inl ⟨∅, Or.inr rfl, τ, hτ, by simp, by rwa [joinL_empty]⟩
  · exact Or.inr ⟨σ, Or.inl hσ, τ, hτ, hστ, hz⟩
  · exact Or.inr ⟨∅, Or.inr rfl, τ, hτ, by simp, by rwa [joinR_empty]⟩

private lemma sums_of_mem_face_joinL {σ : Finset V₀} {τ : Finset V₁} {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ}
    (hz : z ∈ face (joinL σ τ)) : sA z + sM z = 1 ∧ sB z = 0 ∧ 0 ≤ sA z ∧ 0 ≤ sM z := by
  obtain ⟨h0, h1, -, -, hw⟩ := mem_face_joinL.1 hz
  exact ⟨h1, by simp [sB, hw], Finset.sum_nonneg fun a _ ↦ h0 _,
    Finset.sum_nonneg fun a _ ↦ h0 _⟩

private lemma sums_of_mem_face_joinR {σ : Finset V₀} {τ : Finset V₂} {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ}
    (hz : z ∈ face (joinR σ τ)) : sM z + sB z = 1 ∧ sA z = 0 ∧ 0 ≤ sB z ∧ 0 ≤ sM z := by
  obtain ⟨h0, h1, -, -, hu⟩ := mem_face_joinR.1 hz
  exact ⟨h1, by simp [sA, hu], Finset.sum_nonneg fun a _ ↦ h0 _,
    Finset.sum_nonneg fun a _ ↦ h0 _⟩

private lemma sM_eq_zero_of_mem_face_joinL_empty {τ : Finset V₁} {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ}
    (hz : z ∈ face (joinL ∅ τ)) : sM z = 0 := by
  obtain ⟨-, -, -, hc, -⟩ := mem_face_joinL.1 hz
  exact Finset.sum_eq_zero fun c _ ↦ hc c (Finset.notMem_empty c)

private lemma sM_eq_zero_of_mem_face_joinR_empty {τ : Finset V₂} {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ}
    (hz : z ∈ face (joinR ∅ τ)) : sM z = 0 := by
  obtain ⟨-, -, -, hc, -⟩ := mem_face_joinR.1 hz
  exact Finset.sum_eq_zero fun c _ ↦ hc c (Finset.notMem_empty c)

variable (β) in
/-- The `A`-end coordinate of a point of the join model with middle weight `≤ 1/2`. -/
private def fA (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) : V₁ → ℝ :=
  (max 0 (1 - 2 * sM z) / max (1 / 2) (1 - sM z)) • pu z + (2 : ℝ) • pushV β (pv z)

variable (γ) in
/-- The `B`-end coordinate of a point of the join model with middle weight `≤ 1/2`. -/
private def fB (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) : V₂ → ℝ :=
  (max 0 (1 - 2 * sM z) / max (1 / 2) (1 - sM z)) • pw z + (2 : ℝ) • pushV γ (pv z)

/-- The middle coordinate of a point of the join model with middle weight `≥ 1/2`. -/
private def fC (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) : V₀ → ℝ := (max (1 / 2) (sM z))⁻¹ • pv z

/-- The cylinder parameter of a point of the join model. -/
private def θJ (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) : unitInterval := cl (1 / 2 - sA z + sB z)

private lemma continuous_fA : Continuous (fA (V₂ := V₂) (V₀ := V₀) β) := by
  refine (((continuous_const.max (continuous_const.sub (continuous_const.mul continuous_sM))).div
    (continuous_const.max (continuous_const.sub continuous_sM)) fun z ↦ ?_).smul continuous_pu).add
    (((continuous_pushV β).comp continuous_pv).const_smul (2 : ℝ))
  exact (lt_of_lt_of_le (by norm_num) (le_max_left _ _)).ne'

private lemma continuous_fB : Continuous (fB (V₁ := V₁) (V₀ := V₀) γ) := by
  refine (((continuous_const.max (continuous_const.sub (continuous_const.mul continuous_sM))).div
    (continuous_const.max (continuous_const.sub continuous_sM)) fun z ↦ ?_).smul continuous_pw).add
    (((continuous_pushV γ).comp continuous_pv).const_smul (2 : ℝ))
  exact (lt_of_lt_of_le (by norm_num) (le_max_left _ _)).ne'

private lemma continuous_fC : Continuous (fC (V₁ := V₁) (V₀ := V₀) (V₂ := V₂)) :=
  ((continuous_const.max continuous_sM).inv₀ fun z ↦
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _)).ne').smul continuous_pv

private lemma continuous_θJ : Continuous (θJ (V₁ := V₁) (V₀ := V₀) (V₂ := V₂)) :=
  continuous_cl.comp ((continuous_const.sub continuous_sA).add continuous_sB)

/-- On a left piece with middle weight `≤ 1/2`, the `A`-end coordinate lies in `τ`. -/
private lemma fA_mem_face {σ : Finset V₀} {τ : Finset V₁} (hστ : σ.image β ⊆ τ)
    {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ} (hz : z ∈ face (joinL σ τ)) (hM : sM z ≤ 1 / 2) :
    fA β z ∈ face τ := by
  obtain ⟨h0, h1, ha, hc, -⟩ := mem_face_joinL.1 hz
  obtain ⟨hs, -, hA0, hM0⟩ := sums_of_mem_face_joinL hz
  have hden : max (1 / 2) (1 - sM z) = 1 - sM z := max_eq_right (by linarith)
  have hnum : max 0 (1 - 2 * sM z) = 1 - 2 * sM z := max_eq_right (by linarith)
  have hpos : 0 < 1 - sM z := by linarith
  refine ⟨fun a ↦ ?_, ?_, fun a haτ ↦ ?_⟩
  · simp only [fA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (div_nonneg (le_max_left _ _) (by positivity)) (h0 _))
      (mul_nonneg (by norm_num) (pushV_nonneg (fun c ↦ h0 _) a))
  · simp only [fA, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_pushV, hden, hnum]
    change (1 - 2 * sM z) / (1 - sM z) * sA z + 2 * sM z = 1
    rw [show sA z = 1 - sM z by linarith, div_mul_cancel₀ _ hpos.ne']
    ring
  · simp only [fA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ha a haτ, pushV_eq_zero hc fun h ↦ haτ (hστ h)]
    ring

private lemma fB_mem_face {σ : Finset V₀} {τ : Finset V₂} (hστ : σ.image γ ⊆ τ)
    {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ} (hz : z ∈ face (joinR σ τ)) (hM : sM z ≤ 1 / 2) :
    fB γ z ∈ face τ := by
  obtain ⟨h0, h1, hb, hc, -⟩ := mem_face_joinR.1 hz
  obtain ⟨hs, -, hB0, hM0⟩ := sums_of_mem_face_joinR hz
  have hden : max (1 / 2) (1 - sM z) = 1 - sM z := max_eq_right (by linarith)
  have hnum : max 0 (1 - 2 * sM z) = 1 - 2 * sM z := max_eq_right (by linarith)
  have hpos : 0 < 1 - sM z := by linarith
  refine ⟨fun b ↦ ?_, ?_, fun b hbτ ↦ ?_⟩
  · simp only [fB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (div_nonneg (le_max_left _ _) (by positivity)) (h0 _))
      (mul_nonneg (by norm_num) (pushV_nonneg (fun c ↦ h0 _) b))
  · simp only [fB, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_pushV, hden, hnum]
    change (1 - 2 * sM z) / (1 - sM z) * sB z + 2 * sM z = 1
    rw [show sB z = 1 - sM z by linarith, div_mul_cancel₀ _ hpos.ne']
    ring
  · simp only [fB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hb b hbτ, pushV_eq_zero hc fun h ↦ hbτ (hστ h)]
    ring

private lemma fC_mem_face {σ : Finset V₀} {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ} (h0 : ∀ x, 0 ≤ z x)
    (hc : ∀ c ∉ σ, pv z c = 0) (hM : 1 / 2 ≤ sM z) : fC z ∈ face σ := by
  have hpos : 0 < sM z := by linarith
  have hmax : max (1 / 2) (sM z) = sM z := max_eq_right hM
  refine ⟨fun c ↦ ?_, ?_, fun c hcσ ↦ ?_⟩
  · simp only [fC, hmax, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hpos.le) (h0 _)
  · simp only [fC, hmax, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hpos.ne'
  · simp [fC, hc c hcσ]

variable (β γ) in
/-- The point of the join model at height `s` over `t` in the cylinder. -/
private def cylPt (t : V₀ → ℝ) (s : ℝ) : V₁ ⊕ V₀ ⊕ V₂ → ℝ :=
  mk3 (max 0 (1 - 2 * s) • pushV β t) ((1 - |1 - 2 * s|) • t) (max 0 (2 * s - 1) • pushV γ t)

private lemma continuous_cylPt : Continuous fun p : (V₀ → ℝ) × ℝ ↦ cylPt β γ p.1 p.2 := by
  have hs : Continuous fun p : (V₀ → ℝ) × ℝ ↦ p.2 := continuous_snd
  exact continuous_mk3
    ((continuous_const.max (continuous_const.sub (continuous_const.mul hs))).smul
      ((continuous_pushV β).comp continuous_fst))
    ((continuous_const.sub (continuous_const.sub (continuous_const.mul hs)).abs).smul
      continuous_fst)
    ((continuous_const.max ((continuous_const.mul hs).sub continuous_const)).smul
      ((continuous_pushV γ).comp continuous_fst))

private lemma cylPt_mem_face_joinL {σ : Finset V₀} {τ : Finset V₁} (hστ : σ.image β ⊆ τ)
    {t : V₀ → ℝ} (ht : t ∈ face σ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    cylPt β γ t s ∈ face (joinL σ τ) := by
  have hab : |1 - 2 * s| = 1 - 2 * s := abs_of_nonneg (by linarith)
  have hm1 : max 0 (1 - 2 * s) = 1 - 2 * s := max_eq_right (by linarith)
  have hm2 : max 0 (2 * s - 1) = 0 := max_eq_left (by linarith)
  have hpt : pushV β t ∈ face τ := face_mono hστ (pushV_mem_face ht)
  refine mem_face_joinL.2 ⟨fun x ↦ ?_, ?_, fun a ha ↦ ?_, fun c hc ↦ ?_, ?_⟩
  · rcases x with a | c | b
    · exact mul_nonneg (le_max_left _ _) (hpt.1 a)
    · exact mul_nonneg (by rw [hab]; linarith) (ht.1 c)
    · exact mul_nonneg (le_max_left _ _) (pushV_nonneg ht.1 b)
  · simp only [cylPt, pu_mk3, pv_mk3, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      sum_pushV, ht.2.1, hab, hm1]
    ring
  · simp [cylPt, hpt.2.2 a ha]
  · simp [cylPt, ht.2.2 c hc]
  · simp [cylPt, hm2]

private lemma cylPt_mem_face_joinR {σ : Finset V₀} {τ : Finset V₂} (hστ : σ.image γ ⊆ τ)
    {t : V₀ → ℝ} (ht : t ∈ face σ) {s : ℝ} (hs0 : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    cylPt β γ t s ∈ face (joinR σ τ) := by
  have hab : |1 - 2 * s| = 2 * s - 1 := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
  have hm1 : max 0 (1 - 2 * s) = 0 := max_eq_left (by linarith)
  have hm2 : max 0 (2 * s - 1) = 2 * s - 1 := max_eq_right (by linarith)
  have hpt : pushV γ t ∈ face τ := face_mono hστ (pushV_mem_face ht)
  refine mem_face_joinR.2 ⟨fun x ↦ ?_, ?_, fun b hb ↦ ?_, fun c hc ↦ ?_, ?_⟩
  · rcases x with a | c | b
    · exact mul_nonneg (le_max_left _ _) (pushV_nonneg ht.1 a)
    · exact mul_nonneg (by rw [hab]; linarith) (ht.1 c)
    · exact mul_nonneg (le_max_left _ _) (hpt.1 b)
  · simp only [cylPt, pw_mk3, pv_mk3, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      sum_pushV, ht.2.1, hab, hm2]
    ring
  · simp [cylPt, hpt.2.2 b hb]
  · simp [cylPt, ht.2.2 c hc]
  · simp [cylPt, hm1]

private lemma joinL_mem_joinS {σ : Finset V₀} (hσ : σ ∈ S₀ ∨ σ = ∅) {τ : Finset V₁}
    (hτ : τ ∈ S₁) (hστ : σ.image β ⊆ τ) : joinL σ τ ∈ joinS S₀ S₁ S₂ β γ := by
  rcases hσ with hσ | rfl
  · exact Or.inl ⟨σ, hσ, τ, hτ, hστ, rfl⟩
  · exact Or.inr (Or.inl ⟨τ, hτ, joinL_empty τ⟩)

private lemma joinR_mem_joinS {σ : Finset V₀} (hσ : σ ∈ S₀ ∨ σ = ∅) {τ : Finset V₂}
    (hτ : τ ∈ S₂) (hστ : σ.image γ ⊆ τ) : joinR σ τ ∈ joinS S₀ S₁ S₂ β γ := by
  rcases hσ with hσ | rfl
  · exact Or.inr (Or.inr (Or.inl ⟨σ, hσ, τ, hτ, hστ, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨τ, hτ, joinR_empty τ⟩))

variable (hβ : ∀ J ∈ S₀, ∃ τ ∈ S₁, J.image β ⊆ τ) (hγ : ∀ J ∈ S₀, ∃ τ ∈ S₂, J.image γ ⊆ τ)

include hβ hγ

private lemma cylPt_mem {t : V₀ → ℝ} (ht : t ∈ realS S₀) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    cylPt β γ t s ∈ realS (joinS S₀ S₁ S₂ β γ) := by
  obtain ⟨σ, hσ, ht⟩ := mem_realS.1 ht
  rcases le_total s (1 / 2) with h | h
  · obtain ⟨τ, hτ, hστ⟩ := hβ σ hσ
    exact mem_realS.2 ⟨_, joinL_mem_joinS (Or.inl hσ) hτ hστ,
      cylPt_mem_face_joinL hστ ht hs0 h⟩
  · obtain ⟨τ, hτ, hστ⟩ := hγ σ hσ
    exact mem_realS.2 ⟨_, joinR_mem_joinS (Or.inl hσ) hτ hστ,
      cylPt_mem_face_joinR hστ ht h hs1⟩

omit hβ hγ in
private lemma mk3_left_mem {a : V₁ → ℝ} (ha : a ∈ realS S₁) :
    mk3 a 0 0 ∈ realS (joinS S₀ S₁ S₂ β γ) := by
  obtain ⟨τ, hτ, ha⟩ := mem_realS.1 ha
  refine mem_realS.2 ⟨_, joinL_mem_joinS (Or.inr rfl) hτ (by simp), mem_face_joinL.2
    ⟨fun x ↦ ?_, by simpa using ha.2.1, fun a' h ↦ ha.2.2 a' h, fun c _ ↦ rfl, rfl⟩⟩
  rcases x with a' | c | b
  · exact ha.1 a'
  · exact le_rfl
  · exact le_rfl

omit hβ hγ in
private lemma mk3_right_mem {b : V₂ → ℝ} (hb : b ∈ realS S₂) :
    mk3 0 0 b ∈ realS (joinS S₀ S₁ S₂ β γ) := by
  obtain ⟨τ, hτ, hb⟩ := mem_realS.1 hb
  refine mem_realS.2 ⟨_, joinR_mem_joinS (Or.inr rfl) hτ (by simp), mem_face_joinR.2
    ⟨fun x ↦ ?_, by simpa using hb.2.1, fun b' h ↦ hb.2.2 b' h, fun c _ ↦ rfl, rfl⟩⟩
  rcases x with a | c | b'
  · exact le_rfl
  · exact le_rfl
  · exact hb.1 b'

omit hβ hγ in
private lemma cylPt_zero (t : V₀ → ℝ) : cylPt β γ t 0 = mk3 (pushV β t) 0 0 := by
  simp only [cylPt, mul_zero, sub_zero, abs_one, sub_self, zero_smul, zero_sub]
  rw [max_eq_right zero_le_one, max_eq_left (by norm_num), one_smul, zero_smul]

omit hβ hγ in
private lemma cylPt_one (t : V₀ → ℝ) : cylPt β γ t 1 = mk3 0 0 (pushV γ t) := by
  simp only [cylPt, mul_one]
  rw [max_eq_left (by norm_num), show (1 : ℝ) - |1 - 2| = 0 by norm_num,
    show (2 : ℝ) - 1 = 1 by norm_num, max_eq_right zero_le_one, zero_smul, zero_smul, one_smul]

/-- The embedding of the double mapping cylinder of simplicial maps into the join model. -/
private def iMap : C(DMC (pushR β hβ) (pushR γ hγ), realS (joinS S₀ S₁ S₂ β γ)) where
  toFun := desc (fun a ↦ ⟨mk3 a 0 0, mk3_left_mem a.2⟩) (fun b ↦ ⟨mk3 0 0 b, mk3_right_mem b.2⟩)
    (fun t s ↦ ⟨cylPt β γ t s, cylPt_mem hβ hγ t.2 s.2.1 s.2.2⟩)
    (fun t ↦ Subtype.ext (by simp only [Set.Icc.coe_zero]; exact cylPt_zero (t : V₀ → ℝ)))
    (fun t ↦ Subtype.ext (by simp only [Set.Icc.coe_one]; exact cylPt_one (t : V₀ → ℝ)))
  continuous_toFun := continuous_desc
    (Continuous.subtype_mk (continuous_mk3 continuous_subtype_val continuous_const
      continuous_const) _)
    (Continuous.subtype_mk (continuous_mk3 continuous_const continuous_const
      continuous_subtype_val) _)
    (Continuous.subtype_mk (continuous_cylPt.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))) _)

omit hβ hγ in
private lemma sA_eq_zero_or_sB_eq_zero {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ}
    (hz : z ∈ realS (joinS S₀ S₁ S₂ β γ)) : sA z = 0 ∨ sB z = 0 := by
  rcases mem_realS_joinS hz with ⟨σ, -, τ, -, -, hzf⟩ | ⟨σ, -, τ, -, -, hzf⟩
  · exact Or.inr (sums_of_mem_face_joinL hzf).2.1
  · exact Or.inl (sums_of_mem_face_joinR hzf).2.1

private lemma fA_mem {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ} (hz : z ∈ realS (joinS S₀ S₁ S₂ β γ))
    (h : sM z ≤ 1 / 2 ∧ sB z = 0) : fA β z ∈ realS S₁ := by
  rcases mem_realS_joinS hz with ⟨σ, -, τ, hτ, hστ, hzf⟩ | ⟨σ, -, τ, -, -, hzf⟩
  · exact mem_realS.2 ⟨τ, hτ, fA_mem_face hστ hzf h.1⟩
  · have := sums_of_mem_face_joinR hzf
    linarith [h.1, h.2, this.1]

private lemma fB_mem {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ} (hz : z ∈ realS (joinS S₀ S₁ S₂ β γ))
    (h : sM z ≤ 1 / 2 ∧ sA z = 0) : fB γ z ∈ realS S₂ := by
  rcases mem_realS_joinS hz with ⟨σ, -, τ, -, -, hzf⟩ | ⟨σ, -, τ, hτ, hστ, hzf⟩
  · have := sums_of_mem_face_joinL hzf
    linarith [h.1, h.2, this.1]
  · exact mem_realS.2 ⟨τ, hτ, fB_mem_face hστ hzf h.1⟩

omit hβ hγ in
private lemma fC_mem {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ} (hz : z ∈ realS (joinS S₀ S₁ S₂ β γ))
    (h : 1 / 2 ≤ sM z) : fC z ∈ realS S₀ := by
  rcases mem_realS_joinS hz with ⟨σ, hσ, τ, -, -, hzf⟩ | ⟨σ, hσ, τ, -, -, hzf⟩
  · rcases hσ with hσ | rfl
    · obtain ⟨h0, -, -, hc, -⟩ := mem_face_joinL.1 hzf
      exact mem_realS.2 ⟨σ, hσ, fC_mem_face h0 hc h⟩
    · linarith [sM_eq_zero_of_mem_face_joinL_empty hzf]
  · rcases hσ with hσ | rfl
    · obtain ⟨h0, -, -, hc, -⟩ := mem_face_joinR.1 hzf
      exact mem_realS.2 ⟨σ, hσ, fC_mem_face h0 hc h⟩
    · linarith [sM_eq_zero_of_mem_face_joinR_empty hzf]

omit hβ hγ in
private lemma half_le_sM {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ} (hz : z ∈ realS (joinS S₀ S₁ S₂ β γ))
    (h₁ : ¬ (sM z ≤ 1 / 2 ∧ sB z = 0)) (h₂ : ¬ (sM z ≤ 1 / 2 ∧ sA z = 0)) : 1 / 2 ≤ sM z := by
  by_contra h
  push Not at h
  rcases sA_eq_zero_or_sB_eq_zero hz with h' | h'
  · exact h₂ ⟨h.le, h'⟩
  · exact h₁ ⟨h.le, h'⟩

/-- The inverse map from the join model to the double mapping cylinder. -/
private def jFun (z : realS (joinS S₀ S₁ S₂ β γ)) : DMC (pushR β hβ) (pushR γ hγ) :=
  if h₁ : sM z.1 ≤ 1 / 2 ∧ sB z.1 = 0 then inA ⟨fA β z.1, fA_mem hβ hγ z.2 h₁⟩
  else if h₂ : sM z.1 ≤ 1 / 2 ∧ sA z.1 = 0 then inB ⟨fB γ z.1, fB_mem hβ hγ z.2 h₂⟩
  else cyl ⟨fC z.1, fC_mem z.2 (half_le_sM z.2 h₁ h₂)⟩ (θJ z.1)

omit hβ hγ in
private lemma sums_eq_one {z : V₁ ⊕ V₀ ⊕ V₂ → ℝ} (hz : z ∈ realS (joinS S₀ S₁ S₂ β γ)) :
    sA z + sM z + sB z = 1 := by
  obtain ⟨J, -, hzJ⟩ := mem_realS.1 hz
  have := hzJ.2.1
  rw [sum_eq_pu_pv_pw] at this
  exact this

private lemma jFun_of_P₃ (z : realS (joinS S₀ S₁ S₂ β γ)) (hz : 1 / 2 ≤ sM z.1) :
    jFun hβ hγ z = cyl ⟨fC z.1, fC_mem z.2 hz⟩ (θJ z.1) := by
  have hsum := sums_eq_one z.2
  by_cases h₁ : sM z.1 ≤ 1 / 2 ∧ sB z.1 = 0
  · have hM : sM z.1 = 1 / 2 := le_antisymm h₁.1 hz
    rw [jFun, dif_pos h₁]
    have hθ : θJ z.1 = 0 := cl_of_le (by rw [h₁.2]; linarith)
    rw [hθ, cyl_zero]
    congr 1
    apply Subtype.ext
    simp only [coe_pushR, fA, fC, hM]
    rw [show max (0 : ℝ) (1 - 2 * (1 / 2)) = 0 by norm_num, zero_div, zero_smul, zero_add,
      show max (1 / 2 : ℝ) (1 / 2) = 1 / 2 by norm_num, pushV_smul]
    norm_num
  · by_cases h₂ : sM z.1 ≤ 1 / 2 ∧ sA z.1 = 0
    · have hM : sM z.1 = 1 / 2 := le_antisymm h₂.1 hz
      rw [jFun, dif_neg h₁, dif_pos h₂]
      have hθ : θJ z.1 = 1 := cl_of_ge (by rw [h₂.2]; linarith)
      rw [hθ, cyl_one]
      congr 1
      apply Subtype.ext
      simp only [coe_pushR, fB, fC, hM]
      rw [show max (0 : ℝ) (1 - 2 * (1 / 2)) = 0 by norm_num, zero_div, zero_smul, zero_add,
        show max (1 / 2 : ℝ) (1 / 2) = 1 / 2 by norm_num, pushV_smul]
      norm_num
    · rw [jFun, dif_neg h₁, dif_neg h₂]

private lemma continuous_jFun : Continuous (jFun hβ hγ) := by
  have hM : Continuous fun z : realS (joinS S₀ S₁ S₂ β γ) ↦ sM z.1 :=
    continuous_sM.comp continuous_subtype_val
  have hA : Continuous fun z : realS (joinS S₀ S₁ S₂ β γ) ↦ sA z.1 :=
    continuous_sA.comp continuous_subtype_val
  have hB : Continuous fun z : realS (joinS S₀ S₁ S₂ β γ) ↦ sB z.1 :=
    continuous_sB.comp continuous_subtype_val
  let P₁ : Set (realS (joinS S₀ S₁ S₂ β γ)) := {z | sM z.1 ≤ 1 / 2 ∧ sB z.1 = 0}
  let P₂ : Set (realS (joinS S₀ S₁ S₂ β γ)) := {z | sM z.1 ≤ 1 / 2 ∧ sA z.1 = 0}
  let P₃ : Set (realS (joinS S₀ S₁ S₂ β γ)) := {z | 1 / 2 ≤ sM z.1}
  have c₁ : IsClosed P₁ := (isClosed_le hM continuous_const).inter (isClosed_eq hB continuous_const)
  have c₂ : IsClosed P₂ := (isClosed_le hM continuous_const).inter (isClosed_eq hA continuous_const)
  have c₃ : IsClosed P₃ := isClosed_le continuous_const hM
  have hcov : P₁ ∪ P₂ ∪ P₃ = Set.univ := by
    refine Set.eq_univ_of_forall fun z ↦ ?_
    by_cases h : sM z.1 ≤ 1 / 2
    · rcases sA_eq_zero_or_sB_eq_zero z.2 with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inl (Or.inl ⟨h, h'⟩)
    · exact Or.inr (le_of_lt (not_le.1 h))
  have h₁ : ContinuousOn (jFun hβ hγ) P₁ := by
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous fun z : P₁ ↦ (inA ⟨fA β z.1.1, fA_mem hβ hγ z.1.2 z.2⟩ :
        DMC (pushR β hβ) (pushR γ hγ)) :=
      continuous_inA.comp (Continuous.subtype_mk ((continuous_fA (β := β)).comp
        (continuous_subtype_val.comp continuous_subtype_val)) _)
    refine hc.congr fun z ↦ ?_
    change _ = jFun hβ hγ z.1
    rw [jFun, dif_pos (show sM z.1.1 ≤ 1 / 2 ∧ sB z.1.1 = 0 from z.2)]
  have h₂ : ContinuousOn (jFun hβ hγ) P₂ := by
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous fun z : P₂ ↦ (inB ⟨fB γ z.1.1, fB_mem hβ hγ z.1.2 z.2⟩ :
        DMC (pushR β hβ) (pushR γ hγ)) :=
      continuous_inB.comp (Continuous.subtype_mk ((continuous_fB (γ := γ)).comp
        (continuous_subtype_val.comp continuous_subtype_val)) _)
    refine hc.congr fun z ↦ ?_
    have hn : ¬ (sM z.1.1 ≤ 1 / 2 ∧ sB z.1.1 = 0) := fun h ↦ by
      have := sums_eq_one z.1.2
      linarith [z.2.1, z.2.2, h.2]
    change _ = jFun hβ hγ z.1
    rw [jFun, dif_neg hn, dif_pos (show sM z.1.1 ≤ 1 / 2 ∧ sA z.1.1 = 0 from z.2)]
  have h₃ : ContinuousOn (jFun hβ hγ) P₃ := by
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous fun z : P₃ ↦ (cyl ⟨fC z.1.1, fC_mem z.1.2 z.2⟩ (θJ z.1.1) :
        DMC (pushR β hβ) (pushR γ hγ)) :=
      continuous_cyl.comp ((Continuous.subtype_mk (continuous_fC.comp
        (continuous_subtype_val.comp continuous_subtype_val)) _).prodMk
        (continuous_θJ.comp (continuous_subtype_val.comp continuous_subtype_val)))
    exact hc.congr fun z ↦ (jFun_of_P₃ hβ hγ z.1 z.2).symm
  refine continuousOn_univ.1 ?_
  rw [← hcov]
  exact (h₁.union_of_isClosed h₂ c₁ c₂).union_of_isClosed h₃ (c₁.union c₂) c₃

/-- The inverse map, bundled. -/
private def jMap : C(realS (joinS S₀ S₁ S₂ β γ), DMC (pushR β hβ) (pushR γ hγ)) :=
  ⟨jFun hβ hγ, continuous_jFun hβ hγ⟩

omit hβ hγ in
private lemma sums_cylPt {t : V₀ → ℝ} (ht : ∑ c, t c = 1) (T : ℝ) :
    sA (cylPt β γ t T) = max 0 (1 - 2 * T) ∧ sM (cylPt β γ t T) = 1 - |1 - 2 * T| ∧
      sB (cylPt β γ t T) = max 0 (2 * T - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [sA, cylPt, pu_mk3, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_pushV, ht,
      mul_one]
  · simp only [sM, cylPt, pv_mk3, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ht, mul_one]
  · simp only [sB, cylPt, pw_mk3, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_pushV, ht,
      mul_one]

omit hβ hγ in
private lemma sum_eq_one_of_mem_realS {V : Type*} [Fintype V] {S : Set (Finset V)} {t : V → ℝ}
    (ht : t ∈ realS S) : ∑ v, t v = 1 := by
  obtain ⟨σ, -, hσ⟩ := mem_realS.1 ht
  exact hσ.2.1

omit hβ hγ in
private lemma pushV_zero {W V : Type*} [Fintype W] [Fintype V] (β : W → V) :
    pushV β (0 : W → ℝ) = 0 := by
  funext a; simp [pushV]

omit hβ hγ in
private def θ₂ (t : unitInterval) : unitInterval := cl (2 * t - 1 / 2)

omit hβ hγ in
private lemma continuous_θ₂ : Continuous θ₂ :=
  continuous_cl.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)

omit hβ hγ in
private lemma θ₂_zero : θ₂ 0 = 0 := cl_of_le (by norm_num)

omit hβ hγ in
private lemma θ₂_one : θ₂ 1 = 1 := cl_of_ge (by norm_num)

private lemma jFun_iMap (x : DMC (pushR β hβ) (pushR γ hγ)) :
    jFun hβ hγ (iMap hβ hγ x) = reparam θ₂ θ₂_zero θ₂_one x := by
  induction x using ind with
  | hA a =>
    change jFun hβ hγ ⟨mk3 a 0 0, _⟩ = inA a
    have h₁ : sM (mk3 (a : V₁ → ℝ) (0 : V₀ → ℝ) (0 : V₂ → ℝ)) ≤ 1 / 2 ∧
        sB (mk3 (a : V₁ → ℝ) (0 : V₀ → ℝ) (0 : V₂ → ℝ)) = 0 := by
      simp only [sM, sB, pv_mk3, pw_mk3, Pi.zero_apply, Finset.sum_const_zero]; norm_num
    rw [jFun, dif_pos h₁]
    congr 1
    apply Subtype.ext
    simp only [fA, pu_mk3, pv_mk3, pushV_zero, smul_zero, add_zero]
    rw [show sM (mk3 (a : V₁ → ℝ) (0 : V₀ → ℝ) (0 : V₂ → ℝ)) = 0 by simp [sM]]
    norm_num
  | hB b =>
    change jFun hβ hγ ⟨mk3 0 0 b, _⟩ = inB b
    have hb1 := sum_eq_one_of_mem_realS b.2
    have h₁ : ¬ (sM (mk3 (0 : V₁ → ℝ) (0 : V₀ → ℝ) (b : V₂ → ℝ)) ≤ 1 / 2 ∧
        sB (mk3 (0 : V₁ → ℝ) (0 : V₀ → ℝ) (b : V₂ → ℝ)) = 0) := by
      rintro ⟨-, h⟩
      simp only [sB, pw_mk3, hb1] at h
      exact one_ne_zero h
    have h₂ : sM (mk3 (0 : V₁ → ℝ) (0 : V₀ → ℝ) (b : V₂ → ℝ)) ≤ 1 / 2 ∧
        sA (mk3 (0 : V₁ → ℝ) (0 : V₀ → ℝ) (b : V₂ → ℝ)) = 0 := by
      simp only [sM, sA, pv_mk3, pu_mk3, Pi.zero_apply, Finset.sum_const_zero]; norm_num
    rw [jFun, dif_neg h₁, dif_pos h₂]
    congr 1
    apply Subtype.ext
    simp only [fB, pw_mk3, pv_mk3, pushV_zero, smul_zero, add_zero]
    rw [show sM (mk3 (0 : V₁ → ℝ) (0 : V₀ → ℝ) (b : V₂ → ℝ)) = 0 by simp [sM]]
    norm_num
  | hC t s =>
    change jFun hβ hγ ⟨cylPt β γ t s, _⟩ = cyl t (θ₂ s)
    have ht1 := sum_eq_one_of_mem_realS t.2
    obtain ⟨hA, hM, hB⟩ := sums_cylPt (β := β) (γ := γ) ht1 (s : ℝ)
    have hs0 := s.2.1
    have hs1 := s.2.2
    rcases le_or_gt (s : ℝ) (1 / 4) with h | h
    · have hab : |1 - 2 * (s : ℝ)| = 1 - 2 * s := abs_of_nonneg (by linarith)
      have h₁ : sM (cylPt β γ (t : V₀ → ℝ) s) ≤ 1 / 2 ∧ sB (cylPt β γ (t : V₀ → ℝ) s) = 0 := by
        rw [hM, hB, hab, max_eq_left (by linarith)]; constructor <;> linarith
      rw [jFun, dif_pos h₁, show θ₂ s = 0 from cl_of_le (by linarith), cyl_zero]
      congr 1
      apply Subtype.ext
      rw [coe_pushR]
      have hpu : pu (cylPt β γ (t : V₀ → ℝ) s) = max 0 (1 - 2 * (s : ℝ)) • pushV β t := rfl
      have hpv : pv (cylPt β γ (t : V₀ → ℝ) s) = (1 - |1 - 2 * (s : ℝ)|) • (t : V₀ → ℝ) := rfl
      simp only [fA, hM, hpu, hpv, hab, pushV_smul, smul_smul]
      rw [max_eq_right (show (0 : ℝ) ≤ 1 - 2 * s by linarith),
        max_eq_right (show (0 : ℝ) ≤ 1 - 2 * (1 - (1 - 2 * s)) by linarith),
        max_eq_right (show (1 / 2 : ℝ) ≤ 1 - (1 - (1 - 2 * s)) by linarith), ← add_smul]
      convert one_smul ℝ (pushV β (t : V₀ → ℝ)) using 2
      have hne : (1 : ℝ) - (1 - (1 - 2 * s)) ≠ 0 := ne_of_gt (by linarith)
      rw [div_mul_eq_mul_div, div_add' _ _ _ hne, div_eq_one_iff_eq hne]
      ring
    rcases le_or_gt (3 / 4) (s : ℝ) with h' | h'
    · have hab : |1 - 2 * (s : ℝ)| = 2 * s - 1 := by
        rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      have h₁ : ¬ (sM (cylPt β γ (t : V₀ → ℝ) s) ≤ 1 / 2 ∧
          sB (cylPt β γ (t : V₀ → ℝ) s) = 0) := by
        rintro ⟨-, h₀⟩
        rw [hB, max_eq_right (by linarith)] at h₀
        linarith
      have h₂ : sM (cylPt β γ (t : V₀ → ℝ) s) ≤ 1 / 2 ∧ sA (cylPt β γ (t : V₀ → ℝ) s) = 0 := by
        rw [hM, hA, hab, max_eq_left (by linarith)]; constructor <;> linarith
      rw [jFun, dif_neg h₁, dif_pos h₂, show θ₂ s = 1 from cl_of_ge (by linarith), cyl_one]
      congr 1
      apply Subtype.ext
      rw [coe_pushR]
      have hpw : pw (cylPt β γ (t : V₀ → ℝ) s) = max 0 (2 * (s : ℝ) - 1) • pushV γ t := rfl
      have hpv : pv (cylPt β γ (t : V₀ → ℝ) s) = (1 - |1 - 2 * (s : ℝ)|) • (t : V₀ → ℝ) := rfl
      simp only [fB, hM, hpw, hpv, hab, pushV_smul, smul_smul]
      rw [max_eq_right (show (0 : ℝ) ≤ 2 * s - 1 by linarith),
        max_eq_right (show (0 : ℝ) ≤ 1 - 2 * (1 - (2 * s - 1)) by linarith),
        max_eq_right (show (1 / 2 : ℝ) ≤ 1 - (1 - (2 * s - 1)) by linarith), ← add_smul]
      convert one_smul ℝ (pushV γ (t : V₀ → ℝ)) using 2
      have hne : (1 : ℝ) - (1 - (2 * s - 1)) ≠ 0 := ne_of_gt (by linarith)
      rw [div_mul_eq_mul_div, div_add' _ _ _ hne, div_eq_one_iff_eq hne]
      ring
    · have hM' : 1 / 2 < sM (cylPt β γ (t : V₀ → ℝ) s) := by
        rw [hM]
        rcases le_total (s : ℝ) (1 / 2) with h'' | h''
        · rw [abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith)]; linarith
      rw [jFun_of_P₃ hβ hγ ⟨cylPt β γ t s, cylPt_mem hβ hγ t.2 s.2.1 s.2.2⟩ hM'.le]
      congr 1
      · apply Subtype.ext
        simp only [fC, max_eq_right hM'.le]
        rw [hM]
        simp only [cylPt, pv_mk3, smul_smul]
        rw [inv_mul_cancel₀ (by linarith), one_smul]
      · simp only [θJ, θ₂, hA, hB]
        congr 1
        rcases le_total (s : ℝ) (1 / 2) with h'' | h''
        · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
        · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring

/-- Points of the join model and their images under `i ∘ j` lie in a common face. -/
private lemma exists_face_iMap_jFun (z : realS (joinS S₀ S₁ S₂ β γ)) :
    ∃ J ∈ joinS S₀ S₁ S₂ β γ, (z : V₁ ⊕ V₀ ⊕ V₂ → ℝ) ∈ face J ∧
      (iMap hβ hγ (jFun hβ hγ z) : V₁ ⊕ V₀ ⊕ V₂ → ℝ) ∈ face J := by
  have hsum := sums_eq_one z.2
  rcases mem_realS_joinS z.2 with ⟨σ, hσ, τ, hτ, hστ, hzf⟩ | ⟨σ, hσ, τ, hτ, hστ, hzf⟩
  · refine ⟨_, joinL_mem_joinS hσ hτ hστ, hzf, ?_⟩
    obtain ⟨hs, hB0, hA0, hM0⟩ := sums_of_mem_face_joinL hzf
    obtain ⟨h0, -, -, hc, -⟩ := mem_face_joinL.1 hzf
    by_cases hM : sM z.1 ≤ 1 / 2
    · rw [jFun, dif_pos ⟨hM, hB0⟩]
      change mk3 (fA β z.1) 0 0 ∈ face (joinL σ τ)
      have hfa := fA_mem_face hστ hzf hM
      refine mem_face_joinL.2 ⟨fun x ↦ ?_, by simpa using hfa.2.1, fun a ha ↦ hfa.2.2 a ha,
        fun c _ ↦ rfl, rfl⟩
      rcases x with a | c | b
      · exact hfa.1 a
      · exact le_rfl
      · exact le_rfl
    · push Not at hM
      rw [jFun_of_P₃ hβ hγ z hM.le]
      change cylPt β γ (fC z.1) (θJ z.1) ∈ face (joinL σ τ)
      have hθ : ((θJ z.1 : unitInterval) : ℝ) = sM z.1 - 1 / 2 := by
        rw [θJ, hB0, coe_cl (by linarith) (by linarith)]; linarith
      refine cylPt_mem_face_joinL hστ (fC_mem_face h0 hc hM.le) ?_ ?_ <;> rw [hθ] <;> linarith
  · refine ⟨_, joinR_mem_joinS hσ hτ hστ, hzf, ?_⟩
    obtain ⟨hs, hA0, hB0, hM0⟩ := sums_of_mem_face_joinR hzf
    obtain ⟨h0, -, -, hc, -⟩ := mem_face_joinR.1 hzf
    by_cases hM : sM z.1 ≤ 1 / 2
    · have h₁ : ¬ (sM z.1 ≤ 1 / 2 ∧ sB z.1 = 0) := fun h ↦ by linarith [h.2]
      rw [jFun, dif_neg h₁, dif_pos ⟨hM, hA0⟩]
      change mk3 0 0 (fB γ z.1) ∈ face (joinR σ τ)
      have hfb := fB_mem_face hστ hzf hM
      refine mem_face_joinR.2 ⟨fun x ↦ ?_, by simpa using hfb.2.1, fun b hb ↦ hfb.2.2 b hb,
        fun c _ ↦ rfl, rfl⟩
      rcases x with a | c | b
      · exact le_rfl
      · exact le_rfl
      · exact hfb.1 b
    · push Not at hM
      rw [jFun_of_P₃ hβ hγ z hM.le]
      change cylPt β γ (fC z.1) (θJ z.1) ∈ face (joinR σ τ)
      have hθ : ((θJ z.1 : unitInterval) : ℝ) = 3 / 2 - sM z.1 := by
        rw [θJ, hA0, coe_cl (by linarith) (by linarith)]; linarith
      refine cylPt_mem_face_joinR hστ (fC_mem_face h0 hc hM.le) ?_ ?_ <;> rw [hθ] <;> linarith

/-- **The join model**: the double mapping cylinder of two simplicial maps is homotopy
equivalent to the realization of the join complex. -/
private lemma nonempty_homotopyEquiv_join :
    Nonempty (ContinuousMap.HomotopyEquiv (DMC (pushR β hβ) (pushR γ hγ))
      (realS (joinS S₀ S₁ S₂ β γ))) := by
  have hleft : (jMap hβ hγ).comp (iMap hβ hγ) =
      reparamCM θ₂ continuous_θ₂ θ₂_zero θ₂_one := by
    ext x
    exact jFun_iMap hβ hγ x
  have hmem : ∀ p : unitInterval × realS (joinS S₀ S₁ S₂ β γ),
      (1 - (p.1 : ℝ)) • (iMap hβ hγ (jMap hβ hγ p.2) : V₁ ⊕ V₀ ⊕ V₂ → ℝ) +
        (p.1 : ℝ) • (p.2 : V₁ ⊕ V₀ ⊕ V₂ → ℝ) ∈ realS (joinS S₀ S₁ S₂ β γ) := by
    intro p
    obtain ⟨J, hJ, hz, hiz⟩ := exists_face_iMap_jFun hβ hγ p.2
    exact mem_realS.2 ⟨J, hJ, convex_face J hiz hz (by linarith [p.1.2.2]) p.1.2.1 (by ring)⟩
  have hHc : Continuous fun p : unitInterval × realS (joinS S₀ S₁ S₂ β γ) ↦
      (1 - (p.1 : ℝ)) • (iMap hβ hγ (jMap hβ hγ p.2) : V₁ ⊕ V₀ ⊕ V₂ → ℝ) +
        (p.1 : ℝ) • (p.2 : V₁ ⊕ V₀ ⊕ V₂ → ℝ) := by
    have hs : Continuous fun p : unitInterval × realS (joinS S₀ S₁ S₂ β γ) ↦
        ((p.1 : unitInterval) : ℝ) := continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub hs).smul (continuous_subtype_val.comp
      (((iMap hβ hγ).comp (jMap hβ hγ)).continuous.comp continuous_snd))).add
      (hs.smul (continuous_subtype_val.comp continuous_snd))
  have hright : ((iMap hβ hγ).comp (jMap hβ hγ)).Homotopic (ContinuousMap.id _) :=
    ⟨⟨⟨fun p ↦ ⟨_, hmem p⟩, hHc.subtype_mk hmem⟩, fun t ↦ by ext; simp,
      fun t ↦ by ext; simp⟩⟩
  exact ⟨⟨iMap hβ hγ, jMap hβ hγ, by rw [hleft]; exact reparamCM_homotopic _ _ _ _, hright⟩⟩

end

end Join

section Assembly

attribute [local simp] coe_pushR

open scoped Classical

noncomputable section

open DMC CategoryTheory

private lemma exists_homotopyEquiv_realS_of {Y : Type} [TopologicalSpace Y]
    (h : ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv Y K.space)) :
    ∃ (V : Type) (_ : Fintype V) (S : Set (Finset V)), S.Finite ∧
      Nonempty (ContinuousMap.HomotopyEquiv Y (realS S)) := by
  obtain ⟨N, K, hK, ⟨e⟩⟩ := h
  obtain ⟨V, hV, S, hS, ⟨f⟩⟩ := exists_realS_homeomorph_space K hK
  exact ⟨V, hV, S, hS, ⟨e.trans f.toHomotopyEquiv⟩⟩

/-- **Finite homotopy type of a collared pushout.** Let `X` be the pushout of the inclusion of a
compact collared subspace `∂M ⊆ M` along `φ : ∂M → S`. If `M`, `∂M` and `S` are homotopy
equivalent to finite polyhedra, so is `X`. -/
private theorem exists_homotopyEquiv_simplicialComplex_of_isPushout
    {M : Type} [TopologicalSpace M] [T2Space M] {Bs : Set M} [CompactSpace Bs]
    {X : Type} [TopologicalSpace X] {Ss : Set X} (φ : C(Bs, Ss)) (κ : C(M, X))
    (hpush : IsPushout
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Bs ⟶ TopCat.of M)
      (TopCat.ofHom φ) (TopCat.ofHom κ)
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Ss ⟶ TopCat.of X))
    (hsurj : ∀ y : X, y ∈ Ss ∨ ∃ m, κ m = y)
    (c : Bs × Set.Ico (0 : ℝ) 1 → M) (hc : IsOpenEmbedding c)
    (hc0 : ∀ (x : Bs) (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (x, t) = x)
    (hM : ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv M K.space))
    (hB : ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv Bs K.space))
    (hS : ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv Ss K.space)) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv X K.space) := by
  obtain ⟨VM, _, SM, -, ⟨aM⟩⟩ := exists_homotopyEquiv_realS_of hM
  obtain ⟨VS, _, SS, -, ⟨aS⟩⟩ := exists_homotopyEquiv_realS_of hS
  obtain ⟨VB, _, SB, hSB, ⟨aB₀⟩⟩ := exists_homotopyEquiv_realS_of hB
  let aB : ContinuousMap.HomotopyEquiv Bs (cubeS SB) :=
    aB₀.trans (realSHomeoCubeS SB).toHomotopyEquiv
  -- `X` is the double mapping cylinder of `∂M ⊆ M` and `φ`
  obtain ⟨e₁⟩ := nonempty_homeomorph_dmc φ κ hpush hsurj c hc hc0
  -- replace `M` and `S` by their models
  obtain ⟨e₂⟩ := nonempty_homotopyEquiv_ends (f := (Subtype.val : Bs → M)) (g := (φ : Bs → Ss))
    aM aS continuous_subtype_val φ.continuous
  -- transfer the attaching maps to the model of `∂M`
  let ι : C(Bs, M) := ⟨Subtype.val, continuous_subtype_val⟩
  let F₀ : C(cubeS SB, realS SM) := aM.toFun.comp (ι.comp aB.invFun)
  let G₀ : C(cubeS SB, realS SS) := aS.toFun.comp (φ.comp aB.invFun)
  obtain ⟨P⟩ := aB.left_inv
  have hPs : Continuous fun p : Bs × unitInterval ↦ P (unitInterval.symm p.2, p.1) :=
    P.continuous.comp ((unitInterval.continuous_symm.comp continuous_snd).prodMk continuous_fst)
  obtain ⟨e₃⟩ := nonempty_homotopyEquiv_of_homotopy
    (f₀ := aM.toFun ∘ Subtype.val) (f₁ := F₀ ∘ aB.toFun) (g₀ := aS.toFun ∘ φ)
    (g₁ := G₀ ∘ aB.toFun)
    (fun x r ↦ aM.toFun (P (unitInterval.symm r, x)))
    (fun x r ↦ aS.toFun (φ (P (unitInterval.symm r, x))))
    (aM.toFun.continuous.comp (continuous_subtype_val.comp hPs))
    (aS.toFun.continuous.comp (φ.continuous.comp hPs))
    (fun x ↦ by simp) (fun x ↦ by simp [F₀, ι]) (fun x ↦ by simp) (fun x ↦ by simp [G₀])
  obtain ⟨e₄⟩ := nonempty_homotopyEquiv_mid aB F₀ G₀ F₀.continuous G₀.continuous
  -- simplicial approximation on a fine subdivision of the model of `∂M`
  obtain ⟨m, hm, β, γ, hβ, hγ, hFβ, hGγ⟩ := exists_simplicialApprox hSB F₀ G₀
  obtain ⟨ew, hew⟩ := exists_homotopyEquiv_gridS SB hm
  have hFβ' : ∀ u : cubeS SB, ∃ τ ∈ SM, (F₀ u : VM → ℝ) ∈ face τ ∧
      (pushR β hβ (ew.toFun u) : VM → ℝ) ∈ face τ := fun u ↦ by
    obtain ⟨τ, hτ, h1, h2⟩ := hFβ u
    exact ⟨τ, hτ, h1, by rw [coe_pushR, hew]; exact h2⟩
  have hGγ' : ∀ u : cubeS SB, ∃ τ ∈ SS, (G₀ u : VS → ℝ) ∈ face τ ∧
      (pushR γ hγ (ew.toFun u) : VS → ℝ) ∈ face τ := fun u ↦ by
    obtain ⟨τ, hτ, h1, h2⟩ := hGγ u
    exact ⟨τ, hτ, h1, by rw [coe_pushR, hew]; exact h2⟩
  have hmemF : ∀ (u : cubeS SB) (r : unitInterval), (1 - (r : ℝ)) • (F₀ u : VM → ℝ) +
      (r : ℝ) • (pushR β hβ (ew.toFun u) : VM → ℝ) ∈ realS SM := fun u r ↦ by
    obtain ⟨τ, hτ, h1, h2⟩ := hFβ' u
    exact mem_realS.2 ⟨τ, hτ, convex_face τ h1 h2 (by linarith [r.2.2]) r.2.1 (by ring)⟩
  have hmemG : ∀ (u : cubeS SB) (r : unitInterval), (1 - (r : ℝ)) • (G₀ u : VS → ℝ) +
      (r : ℝ) • (pushR γ hγ (ew.toFun u) : VS → ℝ) ∈ realS SS := fun u r ↦ by
    obtain ⟨τ, hτ, h1, h2⟩ := hGγ' u
    exact mem_realS.2 ⟨τ, hτ, convex_face τ h1 h2 (by linarith [r.2.2]) r.2.1 (by ring)⟩
  have hr : Continuous fun p : cubeS SB × unitInterval ↦ ((p.2 : unitInterval) : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  obtain ⟨e₅⟩ := nonempty_homotopyEquiv_of_homotopy (f₀ := F₀) (f₁ := pushR β hβ ∘ ew.toFun)
    (g₀ := G₀) (g₁ := pushR γ hγ ∘ ew.toFun)
    (fun u r ↦ ⟨_, hmemF u r⟩) (fun u r ↦ ⟨_, hmemG u r⟩)
    (Continuous.subtype_mk (((continuous_const.sub hr).smul (continuous_subtype_val.comp
      (F₀.continuous.comp continuous_fst))).add (hr.smul (continuous_subtype_val.comp
      (((pushR β hβ).comp ew.toFun).continuous.comp continuous_fst)))) _)
    (Continuous.subtype_mk (((continuous_const.sub hr).smul (continuous_subtype_val.comp
      (G₀.continuous.comp continuous_fst))).add (hr.smul (continuous_subtype_val.comp
      (((pushR γ hγ).comp ew.toFun).continuous.comp continuous_fst)))) _)
    (fun u ↦ Subtype.ext (by simp)) (fun u ↦ Subtype.ext (by simp))
    (fun u ↦ Subtype.ext (by simp)) (fun u ↦ Subtype.ext (by simp))
  obtain ⟨e₆⟩ := nonempty_homotopyEquiv_mid ew (pushR β hβ) (pushR γ hγ) (pushR β hβ).continuous
    (pushR γ hγ).continuous
  obtain ⟨e₇⟩ := nonempty_homotopyEquiv_join hβ hγ
  obtain ⟨N, K, hK, ⟨e₈⟩⟩ := exists_simplicialComplex_homotopyEquiv_realS
    (joinS (gridS SB m) SM SS β γ) (Set.toFinite _)
  exact ⟨N, K, hK, ⟨e₁.toHomotopyEquiv.trans (e₂.symm.trans (e₃.trans (e₄.trans
    (e₅.trans (e₆.trans (e₇.trans e₈))))))⟩⟩

end

end Assembly

section AlgebraicGeometryPart

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP.Analytic MMP.Analytic.ComplexPoints

noncomputable section

private theorem exists_homotopyEquiv_simplicialComplex_of_isEmpty {Y : Type} [TopologicalSpace Y]
    [IsEmpty Y] :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv Y K.space) := by
  obtain ⟨N, K, hK, ⟨e⟩⟩ := exists_simplicialComplex_homotopyEquiv_realS
    (∅ : Set (Finset PEmpty.{1})) Set.finite_empty
  haveI : IsEmpty (realS (∅ : Set (Finset PEmpty.{1}))) :=
    ⟨fun t ↦ by obtain ⟨σ, hσ, -⟩ := mem_realS.1 t.2; exact hσ⟩
  exact ⟨N, K, hK, ⟨(Homeomorph.empty).toHomotopyEquiv.trans e⟩⟩

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

private lemma toScheme_realize (i : Y ⟶ X) (y : ComplexPoints (i ≫ sX)) :
    (realize (sX := i ≫ sX) (sY := sX) i rfl y).toScheme = i y.toScheme := rfl

/-- The realization of a closed immersion is a topological embedding. -/
private lemma isEmbedding_realize_of_isClosedImmersion (i : Y ⟶ X) [IsClosedImmersion i] :
    IsEmbedding (realize (sX := i ≫ sX) (sY := sX) i rfl) := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  let : Y.Over (Spec (.of ℂ)) := ⟨i ≫ sX⟩
  have : i.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have h : realize (sX := i ≫ sX) (sY := sX) i rfl = (homeomorphUnderlyingSpace (X := X)).symm ∘
      MMP.UnderlyingSpace.map (K := ℂ) i ∘ homeomorphUnderlyingSpace (X := Y) :=
    rfl
  rw [h]
  exact (homeomorphUnderlyingSpace (X := X)).symm.isEmbedding.comp
    ((MMP.UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion
      (K := ℂ) i).isEmbedding.comp (homeomorphUnderlyingSpace (X := Y)).isEmbedding)

/-- The `ℂ`-points of a closed subscheme are homeomorphic to the `ℂ`-points of the ambient
scheme over its image. -/
private def realizeHomeomorph (i : Y ⟶ X) [IsClosedImmersion i] (T : Set Y) :
    (toScheme ⁻¹' T : Set (ComplexPoints (i ≫ sX))) ≃ₜ
      (toScheme ⁻¹' (i '' T) : Set (ComplexPoints sX)) := by
  let g : (toScheme ⁻¹' T : Set (ComplexPoints (i ≫ sX))) → ComplexPoints sX :=
    fun y ↦ realize (sX := i ≫ sX) (sY := sX) i rfl y.1
  have hg : IsEmbedding g :=
    (isEmbedding_realize_of_isClosedImmersion i).comp IsEmbedding.subtypeVal
  have hrange : Set.range g = toScheme ⁻¹' (i '' T) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, y.2, (toScheme_realize i y.1).symm⟩
    · rintro ⟨t, ht, hxt⟩
      obtain ⟨y, rfl⟩ := (mem_range_realize_iff_of_isClosedImmersion (sX := sX) i x).2
        ⟨t, hxt⟩
      refine ⟨⟨y, ?_⟩, rfl⟩
      have : i y.toScheme = i t := by rw [← toScheme_realize i y, hxt]
      change y.toScheme ∈ T
      rw [i.isClosedEmbedding.injective this]
      exact ht
  exact hg.toHomeomorph.trans (Homeomorph.setCongr hrange)

/-- No irreducible component of a reduced complex scheme locally of finite type lies in its
singular locus. -/
private lemma not_subset_singularLocus_of_mem_irreducibleComponents (sY : Y ⟶ Spec (.of ℂ))
    [IsReduced Y] [LocallyOfFiniteType sY] :
    ∀ Z ∈ irreducibleComponents Y, ¬ Z ⊆ (MMP.Mori.singularLocus sY : Set Y) := by
  intro Z hZ hsub
  haveI : LocallyOfFinitePresentation sY :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hcl : closure {η} ∈ irreducibleComponents Y := by rwa [hη.def]
  have hfield := isField_stalk_of_closure_mem_irreducibleComponents Y η hcl
  haveI : IsDomain (Y.presheaf.stalk η) := hfield.isDomain
  haveI : IsPrincipalIdealRing (Y.presheaf.stalk η) := hfield.isPrincipalIdealRing
  have hsm : η ∈ sY.smoothLocus :=
    ((MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField sY).1 η).2 inferInstance
  have hsm' : η ∈ MMP.Mori.smoothLocus sY := by rwa [MMP.Mori.smoothLocus_eq_smoothLocus]
  exact (MMP.Mori.mem_singularLocus_iff.1 (hsub (hη.mem))) hsm'

/-- A projective scheme over `ℂ` is a Noetherian topological space. -/
private lemma noetherianSpace_of_isProjective (hX : IsProjective sX) : NoetherianSpace X := by
  haveI := hX.locallyOfFiniteType
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : QuasiCompact sX := hX.quasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  infer_instance

/-- The image under an injective map `i` with range `Z ≠ ∅` of a set containing no irreducible
component of the source is a proper subset of `Z`. -/
private lemma image_ne_of_not_subset_irreducibleComponents {T U : Type*} [TopologicalSpace U]
    (i : U → T) (hinj : Function.Injective i) {Z : Set T} {S : Set U} (hi : Set.range i = Z)
    (hZ : Z ≠ ∅) (hcomp : ∀ C ∈ irreducibleComponents U, ¬ C ⊆ S) : i '' S ≠ Z := by
  intro h
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hZ
  rw [← hi] at hx
  obtain ⟨y, -⟩ := hx
  obtain ⟨C, hC, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
    isIrreducible_singleton
  refine hcomp C hC fun y' _ ↦ ?_
  have : i y' ∈ i '' S := by
    rw [h, ← hi]
    exact ⟨y', rfl⟩
  obtain ⟨y'', hy'', hyy⟩ := this
  rwa [← hinj hyy]

open scoped Manifold ContDiff in
/-- For every closed subset `Z` of a projective complex scheme, the complex points over `Z` are
homotopy equivalent to a finite polyhedron. -/
private theorem exists_model_closeds (hX : IsProjective sX) (Z : Closeds X) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))), K.faces.Finite ∧
      Nonempty (ContinuousMap.HomotopyEquiv
        (toScheme ⁻¹' (Z : Set X) : Set (ComplexPoints sX)) K.space) := by
  haveI := noetherianSpace_of_isProjective hX
  induction Z using WellFoundedLT.induction with
  | _ Z ih =>
  by_cases hZ : (Z : Set X) = ∅
  · haveI : IsEmpty (toScheme ⁻¹' (Z : Set X) : Set (ComplexPoints sX)) :=
      ⟨fun x ↦ by simpa [hZ] using x.2⟩
    exact exists_homotopyEquiv_simplicialComplex_of_isEmpty
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let i := I.subschemeι
  have hi : Set.range i = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hY : IsProjective (i ≫ sX) :=
    Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion i sX
      inferInstance hX
  let Sing := MMP.Mori.singularLocus (i ≫ sX)
  haveI := hY.locallyOfFiniteType
  have hcomp := not_subset_singularLocus_of_mem_irreducibleComponents (i ≫ sX)
  obtain ⟨ι, _, n, Mi, _, _, _, _, _, -, φ, κ, hpush, -, hrange⟩ :=
    MMP.Analytic.exists_isPushout_manifoldWithCorners_boundary (i ≫ sX) hY Sing le_rfl hcomp
  obtain ⟨hMp, hBp, c, hc, hc0⟩ :=
    MMP.exists_collar_and_homotopyEquiv_finite_simplicialComplex (ι := ι) (n := n) (M := Mi)
  let Z' : Closeds X := ⟨i '' (Sing : Set I.subscheme), i.isClosedEmbedding.isClosedMap _
    Sing.isClosed⟩
  have hZ'le : Z' ≤ Z := by
    rintro _ ⟨y, -, rfl⟩
    exact hi.le ⟨y, rfl⟩
  have hZ'ne : Z' ≠ Z := fun h ↦
    image_ne_of_not_subset_irreducibleComponents (⇑i) i.isClosedEmbedding.injective hi hZ hcomp
      (congrArg SetLike.coe h)
  obtain ⟨N', K', hK', ⟨e'⟩⟩ := ih Z' (lt_of_le_of_ne hZ'le hZ'ne)
  have hS : ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv
        (toScheme ⁻¹' (Sing : Set I.subscheme) : Set (ComplexPoints (i ≫ sX))) K.space) :=
    ⟨N', K', hK', ⟨(realizeHomeomorph i (Sing : Set I.subscheme)).toHomotopyEquiv.trans e'⟩⟩
  have hBc : IsCompact {p : Σ j, Mi j |
      p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (Mi p.1)} :=
    IsClosed.isCompact (isClosed_sigma_iff.2 fun j ↦ ModelWithCorners.isClosed_boundary
      (I := modelWithCornersEuclideanQuadrant (n j)) (M := Mi j) (n := ∞) (by simp))
  haveI := isCompact_iff_compactSpace.1 hBc
  have hsurj : ∀ y : ComplexPoints (i ≫ sX),
      y ∈ (toScheme ⁻¹' (Sing : Set I.subscheme) : Set (ComplexPoints (i ≫ sX))) ∨
        ∃ m, κ m = y := by
    refine fun y ↦ or_iff_not_imp_left.2 fun hy ↦ ?_
    obtain ⟨p, hp⟩ : y ∈ Set.range (fun p : {p : Σ j, Mi j |
        p.2 ∉ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (Mi p.1)} ↦ κ p) := by
      rwa [hrange]
    exact ⟨p.1, hp⟩
  obtain ⟨N, K, hK, ⟨e⟩⟩ :=
    exists_homotopyEquiv_simplicialComplex_of_isPushout φ κ hpush hsurj c hc hc0 hMp hBp hS
  refine ⟨N, K, hK, ⟨?_⟩⟩
  exact ((Homeomorph.setCongr (by rw [Set.image_univ, hi])).trans
    ((realizeHomeomorph i Set.univ).symm.trans
    ((Homeomorph.setCongr Set.preimage_univ).trans
      (Homeomorph.Set.univ _)))).toHomotopyEquiv.trans e

end

end AlgebraicGeometryPart

end MMP.FiniteHomotopyType

@[expose] public section

open AlgebraicGeometry
open MMP.Analytic.ComplexPoints

namespace MMP.Analytic

open MMP.FiniteHomotopyType

/-- **Finite homotopy type of a projective complex scheme.** Let `X` be a projective scheme
over `ℂ`. Then its space of complex points `X^an` is homotopy equivalent to a finite
polyhedron: the space of a simplicial complex with finitely many faces in some `ℝ^N`. -/
@[mmp "lem_mmp_projective_finite_homotopy_type"]
public theorem exists_homotopyEquiv_finite_simplicialComplex_of_isProjective
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv (analyticSpace sX) K.space) := by
  obtain ⟨N, K, hK, ⟨e⟩⟩ := exists_model_closeds hX ⊤
  refine ⟨N, K, hK, ⟨?_⟩⟩
  exact ((Homeomorph.Set.univ (ComplexPoints sX)).symm.trans
    (Homeomorph.setCongr (by simp))).toHomotopyEquiv.trans e

end MMP.Analytic
