module

public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension

/-!
# Coordinate changes between charts of the analytification

Let `X` be a scheme locally of finite type over `ℂ`. For affine charts `c`, `d` of `X` with a
polynomial coordinate change `m : ChartHom c d`, the transition homomorphism
`𝒪_{ℂ^{n_c}, z_c(y)} / I_c → 𝒪_{ℂ^{n_d}, z_d(y)} / I_d` composes germs with the polynomial map
`ℂ^{n_d} → ℂ^{n_c}` of `m`. This file shows that it does not depend on the choice of the
polynomials (Hadamard division), that it is functorial, and that it is bijective: on a basic
open of the source chart the generators of the target are quotients of polynomials in the
generators of the source, and composing with this rational map gives the inverse.

Transition maps then transport elements of the local rings between any two charts through a
point: `MMP.Analytic.Chart.transport` is compatible with every transition map.

## Main definitions

* `MMP.Analytic.holPullbackAt`: composition of holomorphic germs with a map that is holomorphic
  near the base point.
* `MMP.Analytic.ChartHom.ofLE`: a coordinate change between two charts with `U_d ⊆ U_c`.
* `MMP.Analytic.ChartHom.comp`: composition of coordinate changes.
* `MMP.Analytic.Chart.IsTransport`: the property characterizing the transport of an element of
  the local ring of one chart at a point to the local ring of another chart at that point.
* `MMP.Analytic.Chart.transport`: the transport of an element of the local ring of one chart at
  a point to the local ring of another chart at that point.

## Main results

* `MMP.Analytic.Chart.exists_eq`: every affine open is the open of a chart.
* `MMP.Analytic.ChartHom.transition_eq`: the transition map does not depend on the coordinate
  change.
* `MMP.Analytic.ChartHom.transition_comp`: the transition maps are functorial.
* `MMP.Analytic.ChartHom.bijective_transition`: the transition maps are bijective.
* `MMP.Analytic.Chart.transport_self`, `MMP.Analytic.Chart.transition_transport`,
  `MMP.Analytic.Chart.transport_transition`: compatibility of the transport with the transition
  maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Filter Opposite

namespace MMP.Analytic

section Germs

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- Composition of holomorphic germs with a map that is holomorphic near the base point. -/
def holPullbackAt {p : E} {q : F} (G : F → E) (hGd : ∀ᶠ x in 𝓝 q, DifferentiableAt ℂ G x)
    (hG : Tendsto G (𝓝 q) (𝓝 p)) : holGerms p →+* holGerms q :=
  (germPullback G hG).restrict _ _ <| by
    rintro _ ⟨f, rfl, hf⟩
    exact ⟨f ∘ G, rfl, ((hG.eventually hf).and hGd).mono fun y hy => hy.1.comp y hy.2⟩

/-- The germ underlying `holPullbackAt G hGd hG g` is the composition of the germ of `g` with
`G`. -/
@[simp]
lemma coe_holPullbackAt {p : E} {q : F} (G : F → E) (hGd : ∀ᶠ x in 𝓝 q, DifferentiableAt ℂ G x)
    (hG : Tendsto G (𝓝 q) (𝓝 p)) (g : holGerms p) :
    (holPullbackAt G hGd hG g : Germ (𝓝 q) ℂ) = (g : Germ (𝓝 p) ℂ).compTendsto G hG :=
  rfl

/-- For a map `G` holomorphic everywhere, `holPullback` agrees with `holPullbackAt`. -/
lemma holPullback_eq_holPullbackAt {p : E} {q : F} (G : F → E) (hGd : Differentiable ℂ G)
    (hG : Tendsto G (𝓝 q) (𝓝 p)) :
    holPullback G hGd hG = holPullbackAt G (Eventually.of_forall hGd) hG :=
  rfl

/-- Composition with `A` and then with `B` is composition with `A ∘ B`. -/
lemma holPullbackAt_holPullbackAt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {p : E} {q : F} {r : G} (A : F → E) (hAd : ∀ᶠ x in 𝓝 q, DifferentiableAt ℂ A x)
    (hA : Tendsto A (𝓝 q) (𝓝 p)) (B : G → F) (hBd : ∀ᶠ x in 𝓝 r, DifferentiableAt ℂ B x)
    (hB : Tendsto B (𝓝 r) (𝓝 q)) (hABd : ∀ᶠ x in 𝓝 r, DifferentiableAt ℂ (A ∘ B) x)
    (g : holGerms p) :
    holPullbackAt B hBd hB (holPullbackAt A hAd hA g) =
      holPullbackAt (A ∘ B) hABd (hA.comp hB) g := by
  apply Subtype.ext
  obtain ⟨f, hf, -⟩ := g.2
  simp only [coe_holPullbackAt, ← hf, Germ.coe_compTendsto]
  rfl

/-- Composition of germs with two maps that agree near the base point gives the same germ. -/
lemma holPullbackAt_congr {p : E} {q : F} {A B : F → E}
    (hAd : ∀ᶠ x in 𝓝 q, DifferentiableAt ℂ A x) (hA : Tendsto A (𝓝 q) (𝓝 p))
    (hBd : ∀ᶠ x in 𝓝 q, DifferentiableAt ℂ B x) (hB : Tendsto B (𝓝 q) (𝓝 p))
    (hAB : A =ᶠ[𝓝 q] B) (g : holGerms p) :
    holPullbackAt A hAd hA g = holPullbackAt B hBd hB g := by
  apply Subtype.ext
  obtain ⟨f, hf, -⟩ := g.2
  simp only [coe_holPullbackAt, ← hf, Germ.coe_compTendsto]
  exact Germ.coe_eq.2 (hAB.mono fun x hx => by simp [hx])

/-- Composition of germs with the identity is the identity. -/
@[simp]
lemma holPullbackAt_id {p : E} (g : holGerms p) :
    holPullbackAt id (Eventually.of_forall fun _ => differentiableAt_id) tendsto_id g = g := by
  apply Subtype.ext
  obtain ⟨f, hf, -⟩ := g.2
  simp only [coe_holPullbackAt, ← hf, Germ.coe_compTendsto]
  rfl

/-- Composition with two holomorphic maps `A`, `B` with `A a = B a` gives congruent germs modulo
any ideal containing the component germs of `A - B` (Hadamard division). -/
lemma holPullbackAt_sub_mem {ι : Type*} [Fintype ι] {a : F} {b : ι → ℂ} {A B : F → ι → ℂ}
    (hAd : ∀ᶠ x in 𝓝 a, DifferentiableAt ℂ A x) (hA : Tendsto A (𝓝 a) (𝓝 b))
    (hBd : ∀ᶠ x in 𝓝 a, DifferentiableAt ℂ B x) (hB : Tendsto B (𝓝 a) (𝓝 b))
    (hAa : A a = b) (hBa : B a = b) (I : Ideal (holGerms a))
    (hI : ∀ i, ∃ g ∈ I, (g : Germ (𝓝 a) ℂ) = ↑(fun x => A x i - B x i)) (g : holGerms b) :
    holPullbackAt A hAd hA g - holPullbackAt B hBd hB g ∈ I := by
  obtain ⟨f, hf, hfd⟩ := g.2
  obtain ⟨g', hg'I, hg'⟩ :=
    (exists_sub_eq_sum_sub_mul_and_comp_sub_comp_mem hfd).2 a A B hAd hBd hAa hBa I hI
  convert hg'I using 1
  apply Subtype.ext
  rw [hg']
  simp only [AddSubgroupClass.coe_sub, coe_holPullbackAt, ← hf, Germ.coe_compTendsto]
  rfl

end Germs

/-! ### Charts and coordinate changes -/

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

open ComplexPoints

/-- Every affine open of a scheme locally of finite type over `ℂ` is the open of a chart. -/
theorem Chart.exists_eq [LocallyOfFiniteType sX] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ c : Chart sX, c.U = U := by
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType sX inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (le_top : U ≤ sX ⁻¹ᵁ ⊤)
  have hb : (baseRingHom sX U).FiniteType := by
    have : baseRingHom sX U =
        (sX.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom := by
      simp only [baseRingHom, Scheme.Hom.appLE]
      rfl
    rw [this]
    exact hft.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective)
  let _ := (baseRingHom sX U).toAlgebra
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hb
  refine ⟨⟨U, hU, n, fun i => f (MvPolynomial.X i), ?_⟩, rfl⟩
  have : MvPolynomial.eval₂Hom (baseRingHom sX U) (fun i => f (MvPolynomial.X i)) =
      f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [RingHom.algebraMap_toAlgebra]
    · intro i; simp
  rw [this]; exact hf

/-- Every `ℂ`-point `y` of `U ∩ V`, with `U` affine, lies in a chart whose open is a basic open
of `U` contained in `V`. -/
theorem Chart.exists_basicOpen [LocallyOfFiniteType sX] {U V : X.Opens} (hU : IsAffineOpen U)
    (y : ComplexPoints sX) (hyU : y.toScheme ∈ U) (hyV : y.toScheme ∈ V) :
    ∃ (f : Γ(X, U)) (e : Chart sX), e.U = X.basicOpen f ∧ X.basicOpen f ≤ V ∧
      y.toScheme ∈ X.basicOpen f := by
  obtain ⟨f, hfV, hyf⟩ := hU.exists_basicOpen_le (V := V) ⟨_, hyV⟩ hyU
  obtain ⟨e, he⟩ := Chart.exists_eq (sX := sX) (hU.basicOpen f)
  exact ⟨f, e, he, hfV, hyf⟩

namespace ChartHom

/-- A coordinate change `c → d` for charts with `U_d ⊆ U_c`: the generators of `c` restricted to
`U_d` are polynomials in the generators of `d`. -/
def ofLE (c d : Chart sX) (h : d.U ≤ c.U) : ChartHom c d where
  le := h
  P i := (d.surjective (X.presheaf.map (homOfLE h).op (c.gen i))).choose
  spec i := (d.surjective (X.presheaf.map (homOfLE h).op (c.gen i))).choose_spec.symm

/-- The composition of coordinate changes. -/
def comp {c d e : Chart sX} (m : ChartHom c d) (m' : ChartHom d e) : ChartHom c e where
  le := m'.le.trans m.le
  P i := MvPolynomial.bind₁ m'.P (m.P i)
  spec i := by
    rw [← m'.res_pres, ← m.spec i, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp]
lemma comp_P {c d e : Chart sX} (m : ChartHom c d) (m' : ChartHom d e) (i : Fin c.n) :
    (m.comp m').P i = MvPolynomial.bind₁ m'.P (m.P i) :=
  rfl

/-- The polynomial map of a composite coordinate change is the composite of the polynomial maps,
in the opposite order. -/
@[simp]
lemma polyMap_comp {c d e : Chart sX} (m : ChartHom c d) (m' : ChartHom d e) :
    (m.comp m').polyMap = m.polyMap ∘ m'.polyMap := by
  funext y i
  exact (m'.eval_polyMap y (m.P i)).symm

/-- The transition map of a coordinate change `c → d` does not depend on the choice of the
coordinate change. -/
theorem transition_eq {c d : Chart sX} (m m' : ChartHom c d) (y : chart (sX := sX) d.U) :
    m.transition y = m'.transition y := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun g => ?_)
  change m.transition y (Chart.StalkRing.mk c _ g) = m'.transition y (Chart.StalkRing.mk c _ g)
  refine (m.transition_mk y g).trans (Eq.trans ?_ (m'.transition_mk y g).symm)
  refine Ideal.Quotient.eq.2 ?_
  rw [holPullback_eq_holPullbackAt, holPullback_eq_holPullbackAt]
  refine holPullbackAt_sub_mem _ _ _ _ (m.coords_incl y).symm (m'.coords_incl y).symm _
    (fun i => ⟨polyGermHom _ (m.P i - m'.P i), Ideal.mem_map_of_mem _ ?_, ?_⟩) g
  · rw [Chart.ideal, RingHom.mem_ker, map_sub, ← m.spec, ← m'.spec, sub_self]
  · simp only [map_sub]
    rfl

/-- The transition map of any coordinate change `c → e` is the composite of the transition maps of
`m : c → d` and `m' : d → e`. -/
theorem transition_comp {c d e : Chart sX} (m : ChartHom c d) (m' : ChartHom d e)
    (m'' : ChartHom c e) (y : chart (sX := sX) e.U) :
    m''.transition y = (m'.transition y).comp (m.transition (m'.incl y)) := by
  rw [transition_eq m'' (m.comp m')]
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun g => ?_)
  change (m.comp m').transition y (Chart.StalkRing.mk c _ g) =
    m'.transition y (m.transition (m'.incl y) (Chart.StalkRing.mk c _ g))
  refine ((m.comp m').transition_mk y g).trans (Eq.trans ?_
    ((congrArg (m'.transition y) (m.transition_mk (m'.incl y) g)).trans
      (m'.transition_mk y _)).symm)
  congr 1
  apply Subtype.ext
  obtain ⟨_, ⟨f, rfl, -⟩⟩ := g
  simp only [coe_holPullback, Germ.coe_compTendsto, polyMap_comp]
  rfl

/-- Functoriality of the transition maps, evaluated at an element. -/
lemma transition_comp_apply {c d e : Chart sX} (m : ChartHom c d) (m' : ChartHom d e)
    (m'' : ChartHom c e) (y : chart (sX := sX) e.U) (x : c.StalkRing (c.coords (m''.incl y))) :
    m''.transition y x = m'.transition y (m.transition (m'.incl y) x) :=
  RingHom.congr_fun (transition_comp m m' m'' y) x

/-! ### The inverse of a transition map over a basic open -/

variable {b e : Chart sX} (m : ChartHom b e)

/-- On a basic open `U_e = D(g)` of `U_b`, the generators of `e` are quotients `a_j / g^K` of
sections over `U_b`, and a section over `U_b` vanishing on `D(g)` is killed by a power of `g`. -/
lemma exists_localization_data {g : Γ(X, b.U)} (hg : e.U = X.basicOpen g) :
    IsUnit (X.presheaf.map (homOfLE m.le).op g) ∧
    (∃ (K : ℕ) (a : Fin e.n → Γ(X, b.U)), ∀ j,
      X.presheaf.map (homOfLE m.le).op (a j) = X.presheaf.map (homOfLE m.le).op g ^ K * e.gen j) ∧
    ∀ z : Γ(X, b.U), X.presheaf.map (homOfLE m.le).op z = 0 → ∃ L : ℕ, g ^ L * z = 0 := by
  obtain ⟨le, P, spec⟩ := m
  obtain ⟨U, hU, n, gen, hs⟩ := e
  dsimp only at hg le ⊢
  subst hg
  let := (X.presheaf.map (homOfLE le).op).hom.toAlgebra
  have : IsLocalization.Away g Γ(X, X.basicOpen g) := b.isAffineOpen.isLocalization_basicOpen g
  refine ⟨IsLocalization.Away.algebraMap_isUnit g, ?_, fun z hz => ?_⟩
  · obtain ⟨⟨_, K, rfl⟩, hK⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers g)
      Finset.univ gen
    choose a ha using fun j => hK j (Finset.mem_univ j)
    refine ⟨K, a, fun j => ?_⟩
    have := ha j
    simp only [Algebra.smul_def, map_pow] at this
    exact this
  · obtain ⟨⟨_, L, rfl⟩, hL⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers g) Γ(X, X.basicOpen g) z).1 hz
    exact ⟨L, hL⟩

/-- Clearing denominators: substituting `a_j / g^K` for the generators of `e` in a polynomial
`r` and multiplying by a power of `g` gives a polynomial in the generators of `b`. -/
lemma exists_res_pres_eq_pow_mul_pres (G : MvPolynomial (Fin b.n) ℂ)
    (A : Fin e.n → MvPolynomial (Fin b.n) ℂ) (K : ℕ)
    (hA : ∀ j, X.presheaf.map (homOfLE m.le).op (b.pres (A j)) =
      X.presheaf.map (homOfLE m.le).op (b.pres G) ^ K * e.gen j)
    (r : MvPolynomial (Fin e.n) ℂ) :
    ∃ (N : ℕ) (R : MvPolynomial (Fin b.n) ℂ),
      (∀ x, MvPolynomial.eval x G ≠ 0 → MvPolynomial.eval x R = MvPolynomial.eval x G ^ N *
        MvPolynomial.eval (fun j => MvPolynomial.eval x (A j) / MvPolynomial.eval x G ^ K) r) ∧
      X.presheaf.map (homOfLE m.le).op (b.pres R) =
        X.presheaf.map (homOfLE m.le).op (b.pres G) ^ N * e.pres r := by
  induction r using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, MvPolynomial.C a, fun x _ => by simp, ?_⟩
    simp only [Chart.pres, MvPolynomial.eval₂Hom_C, pow_zero, one_mul]
    exact baseRingHom_res m.le a
  | add p q hp hq =>
    obtain ⟨N₁, R₁, h₁, h₁'⟩ := hp
    obtain ⟨N₂, R₂, h₂, h₂'⟩ := hq
    refine ⟨N₁ + N₂, R₁ * G ^ N₂ + R₂ * G ^ N₁, fun x hx => ?_, ?_⟩
    · simp only [map_add, map_mul, map_pow, h₁ x hx, h₂ x hx]
      ring
    · simp only [map_add, map_mul, map_pow, h₁', h₂']
      ring
  | mul_X p j hp =>
    obtain ⟨N, R, h, h'⟩ := hp
    refine ⟨N + K, R * A j, fun x hx => ?_, ?_⟩
    · simp only [map_mul, h x hx, MvPolynomial.eval_X]
      field_simp
      ring
    · rw [map_mul, map_mul, map_mul, h', hA, pow_add]
      simp only [Chart.pres, MvPolynomial.eval₂Hom_X']
      ring

/-- A holomorphic germ which becomes the germ of a polynomial `R` with `G^L R ∈ I` after
multiplication by a power of a polynomial `G` not vanishing at the base point lies in the
ideal generated by the relations of the chart. -/
lemma _root_.MMP.Analytic.Chart.mem_map_of_polyGermHom_mul (c : Chart sX) {p : Fin c.n → ℂ}
    (G : MvPolynomial (Fin c.n) ℂ) (hp : MvPolynomial.eval p G ≠ 0)
    {R : MvPolynomial (Fin c.n) ℂ} (hR : ∃ L : ℕ, c.pres G ^ L * c.pres R = 0) {φ : holGerms p}
    {N : ℕ} (h : polyGermHom p G ^ N * φ = polyGermHom p R) :
    φ ∈ c.ideal.map (polyGermHom p) := by
  obtain ⟨L, hL⟩ := hR
  have hmem : polyGermHom p (G ^ L * R) ∈ c.ideal.map (polyGermHom p) :=
    Ideal.mem_map_of_mem _ (by rw [Chart.ideal, RingHom.mem_ker, map_mul, map_pow]; exact hL)
  rw [map_mul, ← h, ← mul_assoc, map_pow, ← pow_add] at hmem
  exact (Ideal.unit_mul_mem_iff_mem _ ((isUnit_polyGermHom p G hp).pow _)).1 hmem

/-- If `G(x)^N f(x) = R(x)` near `p` for polynomials `G`, `R` and a holomorphic `f`, then
`G^N` times the germ of `f` is the germ of `R`. -/
lemma _root_.MMP.Analytic.polyGermHom_pow_mul_eq {n : ℕ} {p : Fin n → ℂ}
    {G R : MvPolynomial (Fin n) ℂ} {N : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : (f : Germ (𝓝 p) ℂ) ∈ holGerms p)
    (h : ∀ᶠ x in 𝓝 p, MvPolynomial.eval x G ^ N * f x = MvPolynomial.eval x R) :
    polyGermHom p G ^ N * ⟨f, hf⟩ = polyGermHom p R := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_polyGermHom, ← Germ.coe_pow,
    ← Germ.coe_mul]
  exact Germ.coe_eq.2 (h.mono fun x hx => by simpa using hx)

/-- **The inverse of a transition map.** If the open of `e` is a basic open `D(g)` of the open of
`b`, then near every point of `e` the rational map `Q = (a_j / g^K)_j : ℂ^{n_b} ⇢ ℂ^{n_e}`
expressing the generators of `e` in those of `b` inverts the transition map of `m`. -/
theorem exists_inverse_of_eq_basicOpen {g : Γ(X, b.U)} (hg : e.U = X.basicOpen g) :
    ∃ (G : MvPolynomial (Fin b.n) ℂ) (Q : (Fin b.n → ℂ) → Fin e.n → ℂ),
      (∀ w : chart (sX := sX) e.U, MvPolynomial.eval (b.coords (m.incl w)) G ≠ 0) ∧
      (∀ x, MvPolynomial.eval x G ≠ 0 → DifferentiableAt ℂ Q x) ∧
      (∀ w : chart (sX := sX) e.U, Q (b.coords (m.incl w)) = e.coords w) ∧
      ∀ (w : chart (sX := sX) e.U)
        (hQd : ∀ᶠ x in 𝓝 (b.coords (m.incl w)), DifferentiableAt ℂ Q x)
        (hQ : Tendsto Q (𝓝 (b.coords (m.incl w))) (𝓝 (e.coords w))),
        (∀ g' ∈ e.ideal.map (polyGermHom (e.coords w)),
          holPullbackAt Q hQd hQ g' ∈ b.ideal.map (polyGermHom (b.coords (m.incl w)))) ∧
        (∀ g' : holGerms (e.coords w),
          m.transition w (Chart.StalkRing.mk b _ (holPullbackAt Q hQd hQ g')) =
            Chart.StalkRing.mk e _ g') ∧
        ∀ g₀ : holGerms (b.coords (m.incl w)),
          Chart.StalkRing.mk b _ (holPullbackAt Q hQd hQ
            (holPullback m.polyMap m.differentiable_polyMap (m.tendsto_polyMap w) g₀)) =
            Chart.StalkRing.mk b _ g₀ := by
  obtain ⟨hunit, ⟨K, a, ha⟩, hker⟩ := m.exists_localization_data hg
  obtain ⟨G, hG⟩ := b.surjective g
  choose A hA using fun j => b.surjective (a j)
  replace hG : b.pres G = g := hG
  replace hA : ∀ j, b.pres (A j) = a j := hA
  have hA' : ∀ j, X.presheaf.map (homOfLE m.le).op (b.pres (A j)) =
      X.presheaf.map (homOfLE m.le).op (b.pres G) ^ K * e.gen j := fun j => by
    rw [hA, hG]; exact ha j
  have hker' : ∀ R, X.presheaf.map (homOfLE m.le).op (b.pres R) = 0 →
      ∃ L : ℕ, b.pres G ^ L * b.pres R = 0 := fun R hR => by
    rw [hG]; exact hker _ hR
  set Q : (Fin b.n → ℂ) → Fin e.n → ℂ :=
    fun x j => MvPolynomial.eval x (A j) / MvPolynomial.eval x G ^ K with hQdef
  have hev : ∀ (w : chart (sX := sX) e.U) (q : MvPolynomial (Fin b.n) ℂ),
      MvPolynomial.eval (b.coords (m.incl w)) q =
        evalHom e.U w (X.presheaf.map (homOfLE m.le).op (b.pres q)) := fun w q => by
    rw [← b.evalHom_pres]
    exact evalHom_res m.le w _
  have hGw : ∀ w : chart (sX := sX) e.U, MvPolynomial.eval (b.coords (m.incl w)) G ≠ 0 :=
    fun w => by rw [hev, hG]; exact (hunit.map (evalHom e.U w)).ne_zero
  have hQd : ∀ x, MvPolynomial.eval x G ≠ 0 → DifferentiableAt ℂ Q x := fun x hx =>
    differentiableAt_pi.2 fun j => by
      have h1 : DifferentiableAt ℂ (fun y => MvPolynomial.eval y (A j)) x :=
        differentiable_eval_mvPolynomial (A j) x
      have h2 : DifferentiableAt ℂ (fun y => MvPolynomial.eval y G) x :=
        differentiable_eval_mvPolynomial G x
      simp only [hQdef]
      fun_prop (disch := exact pow_ne_zero _ hx)
  have hQw : ∀ w : chart (sX := sX) e.U, Q (b.coords (m.incl w)) = e.coords w := fun w => by
    funext j
    simp only [hQdef]
    rw [div_eq_iff (pow_ne_zero _ (hGw w)), hev, hev, hA', map_mul, map_pow]
    simp only [Chart.coords]
    ring
  refine ⟨G, Q, hGw, hQd, hQw, fun w hQd' hQ => ?_⟩
  have hGev : ∀ᶠ x in 𝓝 (b.coords (m.incl w)), MvPolynomial.eval x G ≠ 0 :=
    (differentiable_eval_mvPolynomial G).continuous.continuousAt.eventually_ne (hGw w)
  have hpq : m.polyMap (e.coords w) = b.coords (m.incl w) := (m.coords_incl w).symm
  refine ⟨fun g' hg' => ?_, fun g' => ?_, fun g₀ => ?_⟩
  · refine Ideal.mem_comap.1 ((Ideal.map_le_iff_le_comap.2 (fun r hr => ?_) :
      _ ≤ Ideal.comap (holPullbackAt Q hQd' hQ) _) hg')
    obtain ⟨N, R, hRev, hRρ⟩ := m.exists_res_pres_eq_pow_mul_pres G A K hA' r
    rw [Ideal.mem_comap]
    exact b.mem_map_of_polyGermHom_mul G (hGw w)
      (hker' R (by rw [hRρ, (RingHom.mem_ker).1 hr, mul_zero])) (N := N)
      (polyGermHom_pow_mul_eq (G := G) (R := R) (N := N) (f := fun x => MvPolynomial.eval (Q x) r)
        (holPullbackAt Q hQd' hQ (polyGermHom (e.coords w) r)).2
        (hGev.mono fun x hx => (hRev x hx).symm))
  · rw [transition_mk, holPullback_eq_holPullbackAt]
    have hd : ∀ᶠ x in 𝓝 (e.coords w), DifferentiableAt ℂ (Q ∘ m.polyMap) x :=
      ((m.tendsto_polyMap w).eventually hQd').mono fun x hx =>
        hx.comp x (m.differentiable_polyMap x)
    rw [holPullbackAt_holPullbackAt _ _ _ _ _ _ hd]
    refine Ideal.Quotient.eq.2 ?_
    have hval : (Q ∘ m.polyMap) (e.coords w) = e.coords w := by
      change Q (m.polyMap (e.coords w)) = _
      rw [hpq, hQw]
    have hBG : MvPolynomial.eval (e.coords w) (MvPolynomial.bind₁ m.P G) ≠ 0 := by
      rw [← m.eval_polyMap, hpq]; exact hGw w
    have hBGev : ∀ᶠ x in 𝓝 (e.coords w), MvPolynomial.eval x (MvPolynomial.bind₁ m.P G) ≠ 0 :=
      (differentiable_eval_mvPolynomial _).continuous.continuousAt.eventually_ne hBG
    have key := holPullbackAt_sub_mem hd (hQ.comp (m.tendsto_polyMap w))
      (Eventually.of_forall fun _ => differentiableAt_id) tendsto_id hval rfl
      (e.ideal.map (polyGermHom (e.coords w))) (fun j => ?_) g'
    · rwa [holPullbackAt_id] at key
    have hmem : ((fun x => (Q ∘ m.polyMap) x j - id x j : _ → ℂ) : Germ (𝓝 (e.coords w)) ℂ) ∈
        holGerms (e.coords w) := by
      refine coe_mem_holGerms (hd.mono fun x hx => ?_)
      exact ((differentiableAt_pi.1 hx) j).sub ((differentiableAt_pi.1 differentiableAt_id) j)
    refine ⟨⟨_, hmem⟩, e.mem_map_of_polyGermHom_mul (MvPolynomial.bind₁ m.P G) hBG
      (R := MvPolynomial.bind₁ m.P (A j) - MvPolynomial.bind₁ m.P G ^ K * MvPolynomial.X j)
      ⟨0, ?_⟩ (N := K) ?_, rfl⟩
    · rw [pow_zero, one_mul, map_sub, map_mul, map_pow, ← m.res_pres, ← m.res_pres, hA']
      simp [Chart.pres]
    · refine polyGermHom_pow_mul_eq _ (hBGev.mono fun x hx => ?_)
      have e1 := m.eval_polyMap x (A j)
      have e2 := m.eval_polyMap x G
      simp only [Function.comp_apply, hQdef, id, map_sub, map_mul, map_pow,
        MvPolynomial.eval_X, e1, e2]
      field_simp
  · rw [holPullback_eq_holPullbackAt]
    have hd : ∀ᶠ x in 𝓝 (b.coords (m.incl w)), DifferentiableAt ℂ (m.polyMap ∘ Q) x :=
      hQd'.mono fun x hx => (m.differentiable_polyMap _).comp x hx
    rw [holPullbackAt_holPullbackAt _ _ _ _ _ _ hd]
    refine Ideal.Quotient.eq.2 ?_
    have hval : (m.polyMap ∘ Q) (b.coords (m.incl w)) = b.coords (m.incl w) := by
      change m.polyMap (Q (b.coords (m.incl w))) = _
      rw [hQw, hpq]
    have ht : Tendsto (m.polyMap ∘ Q) (𝓝 (b.coords (m.incl w))) (𝓝 (b.coords (m.incl w))) :=
      (m.tendsto_polyMap w).comp hQ
    obtain ⟨φ, hφ⟩ : ∃ φ : Fin b.n → holGerms (b.coords (m.incl w)), ∀ i,
        (φ i : Germ (𝓝 (b.coords (m.incl w))) ℂ) = ↑(fun x => (m.polyMap ∘ Q) x i - id x i) :=
      ⟨fun i => ⟨_, coe_mem_holGerms (hd.mono fun x hx =>
        ((differentiableAt_pi.1 hx) i).sub ((differentiableAt_pi.1 differentiableAt_id) i))⟩,
        fun i => rfl⟩
    have key := holPullbackAt_sub_mem hd ht
      (Eventually.of_forall fun _ => differentiableAt_id) tendsto_id hval rfl
      (b.ideal.map (polyGermHom (b.coords (m.incl w)))) (fun i => ⟨φ i, ?_, hφ i⟩) g₀
    · rwa [holPullbackAt_id] at key
    obtain ⟨N, R, hRev, hRρ⟩ := m.exists_res_pres_eq_pow_mul_pres G A K hA' (m.P i)
    have hφi : φ i = ⟨_, (φ i).2⟩ := rfl
    rw [hφi]
    simp only [hφ i]
    refine b.mem_map_of_polyGermHom_mul G (hGw w)
      (R := R - G ^ N * MvPolynomial.X i) (hker' _ ?_) (N := N) ?_
    · rw [map_sub, map_mul, map_pow, map_sub, map_mul, map_pow, hRρ, ← m.spec i]
      simp [Chart.pres]
    · refine polyGermHom_pow_mul_eq _ (hGev.mono fun x hx => ?_)
      simp only [Function.comp_apply, polyMap, id, map_sub, map_mul, map_pow,
        MvPolynomial.eval_X, hRev x hx]
      ring

/-- Over a basic open of the source chart, the transition map is bijective at every point. -/
theorem bijective_transition_of_eq_basicOpen {g : Γ(X, b.U)} (hg : e.U = X.basicOpen g)
    (w : chart (sX := sX) e.U) : Function.Bijective (m.transition w) := by
  obtain ⟨G, Q, hGw, hQd, hQw, hinv⟩ := m.exists_inverse_of_eq_basicOpen hg
  have hQd' : ∀ᶠ x in 𝓝 (b.coords (m.incl w)), DifferentiableAt ℂ Q x :=
    ((differentiable_eval_mvPolynomial G).continuous.continuousAt.eventually_ne (hGw w)).mono
      fun x hx => hQd x hx
  have hQ : Tendsto Q (𝓝 (b.coords (m.incl w))) (𝓝 (e.coords w)) := by
    have := (hQd _ (hGw w)).continuousAt.tendsto
    rwa [hQw] at this
  obtain ⟨hI, hright, hleft⟩ := hinv w hQd' hQ
  refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => ?_, fun t => ?_⟩
  · obtain ⟨g₀, rfl⟩ := Ideal.Quotient.mk_surjective t
    change m.transition w (Chart.StalkRing.mk b _ g₀) = 0 at ht
    rw [transition_mk] at ht
    have h1 := hI _ (Ideal.Quotient.eq_zero_iff_mem.1 ht)
    exact (hleft g₀).symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 h1)
  · obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective t
    exact ⟨_, hright g'⟩

end ChartHom

/-- Two charts through a point have a common refinement: a chart through the point whose open
is a basic open of the first chart contained in the second. -/
theorem Chart.exists_refinement [LocallyOfFiniteType sX] (c d : Chart sX) (z : ComplexPoints sX)
    (hc : z.toScheme ∈ c.U) (hd : z.toScheme ∈ d.U) :
    ∃ (f : Γ(X, c.U)) (e : Chart sX), e.U = X.basicOpen f ∧ e.U ≤ d.U ∧ z.toScheme ∈ e.U := by
  obtain ⟨f, e, he, hle, hz⟩ := Chart.exists_basicOpen c.isAffineOpen z hc hd
  exact ⟨f, e, he, he ▸ hle, he ▸ hz⟩

namespace ChartHom

/-- **Transition maps are bijective.** The transition map of a coordinate change is bijective at
every point. -/
theorem bijective_transition [LocallyOfFiniteType sX] {a b : Chart sX} (m : ChartHom a b)
    (w : chart (sX := sX) b.U) : Function.Bijective (m.transition w) := by
  obtain ⟨f, e, he, hle, hz⟩ :=
    Chart.exists_refinement a b w.1 (mem_chart_iff.1 (chart_mono m.le w.2)) (mem_chart_iff.1 w.2)
  have he' : e.U = X.basicOpen (X.presheaf.map (homOfLE m.le).op f) := by
    rw [Scheme.basicOpen_res, he]
    exact (inf_eq_right.2 (he ▸ hle)).symm
  let w' : chart (sX := sX) e.U := ⟨w.1, mem_chart_iff.2 hz⟩
  have h1 := (ofLE a e (he ▸ X.basicOpen_le f)).bijective_transition_of_eq_basicOpen he w'
  have h2 := (ofLE b e hle).bijective_transition_of_eq_basicOpen he' w'
  have hc : ⇑((ofLE a e (he ▸ X.basicOpen_le f)).transition w') =
      (ofLE b e hle).transition w' ∘ m.transition w :=
    funext fun x => transition_comp_apply m (ofLE b e hle) _ w' x
  rw [hc] at h1
  exact (Function.Bijective.of_comp_iff' h2 _).1 h1

end ChartHom

/-! ### Transport of local rings between charts -/

namespace Chart

/-- The property characterizing the transport `t` of `x` from chart `c` to chart `d` at `z`: the
two agree after the transition maps to every common refinement. -/
def IsTransport (c d : Chart sX) (z : ComplexPoints sX) (hc : z ∈ chart (sX := sX) c.U)
    (hd : z ∈ chart (sX := sX) d.U) (x : c.StalkRing (c.coords ⟨z, hc⟩))
    (t : d.StalkRing (d.coords ⟨z, hd⟩)) : Prop :=
  ∀ (e : Chart sX) (he : z ∈ chart (sX := sX) e.U) (m₁ : ChartHom c e) (m₂ : ChartHom d e),
    m₂.transition ⟨z, he⟩ t = m₁.transition ⟨z, he⟩ x

variable [LocallyOfFiniteType sX]

/-- Every element of the local ring of `c` at `z` has a transport to the local ring of `d` at
`z`. -/
lemma exists_isTransport (c d : Chart sX) (z : ComplexPoints sX) (hc : z ∈ chart (sX := sX) c.U)
    (hd : z ∈ chart (sX := sX) d.U) (x : c.StalkRing (c.coords ⟨z, hc⟩)) :
    ∃ t, IsTransport c d z hc hd x t := by
  obtain ⟨f₀, e₀', he₀', hle₀', hz₀'⟩ := Chart.exists_refinement c d z (mem_chart_iff.1 hc)
    (mem_chart_iff.1 hd)
  have hc₀ : e₀'.U ≤ c.U := he₀' ▸ X.basicOpen_le f₀
  set m₁₀ := ChartHom.ofLE c e₀' hc₀
  set m₂₀ := ChartHom.ofLE d e₀' hle₀'
  have hz : z ∈ chart (sX := sX) e₀'.U := mem_chart_iff.2 hz₀'
  obtain ⟨t, ht⟩ := (m₂₀.bijective_transition ⟨z, hz⟩).2 (m₁₀.transition ⟨z, hz⟩ x)
  refine ⟨t, fun e he m₁ m₂ => ?_⟩
  obtain ⟨f, e'', he'', hle'', hz''⟩ := Chart.exists_refinement e₀' e z (mem_chart_iff.1 hz)
    (mem_chart_iff.1 he)
  have h₀ : e''.U ≤ e₀'.U := he'' ▸ X.basicOpen_le f
  set n₀ := ChartHom.ofLE e₀' e'' h₀
  set n := ChartHom.ofLE e e'' hle''
  have hz' : z ∈ chart (sX := sX) e''.U := mem_chart_iff.2 hz''
  apply (n.bijective_transition ⟨z, hz'⟩).1
  have k₂ := ChartHom.transition_comp_apply m₂ n
    (ChartHom.ofLE d e'' (h₀.trans hle₀')) ⟨z, hz'⟩ t
  have k₂' := ChartHom.transition_comp_apply m₂₀ n₀
    (ChartHom.ofLE d e'' (h₀.trans hle₀')) ⟨z, hz'⟩ t
  have k₁ := ChartHom.transition_comp_apply m₁ n
    (ChartHom.ofLE c e'' (h₀.trans hc₀)) ⟨z, hz'⟩ x
  have k₁' := ChartHom.transition_comp_apply m₁₀ n₀
    (ChartHom.ofLE c e'' (h₀.trans hc₀)) ⟨z, hz'⟩ x
  exact k₂.symm.trans (k₂'.trans ((congrArg _ ht).trans (k₁'.symm.trans k₁)))

/-- The transport of an element of the local ring of the chart `c` at `z` to the local ring of
the chart `d` at `z`, through the transition maps to common refinements. -/
def transport (c d : Chart sX) (z : ComplexPoints sX) (hc : z ∈ chart (sX := sX) c.U)
    (hd : z ∈ chart (sX := sX) d.U) (x : c.StalkRing (c.coords ⟨z, hc⟩)) :
    d.StalkRing (d.coords ⟨z, hd⟩) :=
  (exists_isTransport c d z hc hd x).choose

/-- `transport c d z hc hd x` is a transport of `x`. -/
lemma isTransport_transport (c d : Chart sX) (z : ComplexPoints sX)
    (hc : z ∈ chart (sX := sX) c.U) (hd : z ∈ chart (sX := sX) d.U)
    (x : c.StalkRing (c.coords ⟨z, hc⟩)) : IsTransport c d z hc hd x (transport c d z hc hd x) :=
  (exists_isTransport c d z hc hd x).choose_spec

/-- The transport is unique: every transport of `x` equals `transport c d z hc hd x`. -/
lemma eq_transport_of_isTransport {c d : Chart sX} {z : ComplexPoints sX}
    {hc : z ∈ chart (sX := sX) c.U} {hd : z ∈ chart (sX := sX) d.U}
    {x : c.StalkRing (c.coords ⟨z, hc⟩)} {t : d.StalkRing (d.coords ⟨z, hd⟩)}
    (ht : IsTransport c d z hc hd x t) : t = transport c d z hc hd x := by
  obtain ⟨f, e, he, hle, hz⟩ := Chart.exists_refinement c d z (mem_chart_iff.1 hc)
    (mem_chart_iff.1 hd)
  have hz' : z ∈ chart (sX := sX) e.U := mem_chart_iff.2 hz
  have hce : e.U ≤ c.U := he ▸ X.basicOpen_le f
  apply ((ChartHom.ofLE d e hle).bijective_transition ⟨z, hz'⟩).1
  rw [ht e hz' (ChartHom.ofLE c e hce), isTransport_transport c d z hc hd x e hz'
    (ChartHom.ofLE c e hce)]

/-- Transport from a chart to itself is the identity. -/
@[simp]
lemma transport_self (c : Chart sX) (z : ComplexPoints sX) (hc : z ∈ chart (sX := sX) c.U)
    (x : c.StalkRing (c.coords ⟨z, hc⟩)) : transport c c z hc hc x = x :=
  (eq_transport_of_isTransport fun _ _ m₁ m₂ => by rw [ChartHom.transition_eq m₂ m₁]; rfl).symm

/-- Transport to `d` followed by the transition map of `m : ChartHom d d'` is transport to
`d'`. -/
@[simp]
lemma transition_transport {c d d' : Chart sX} (m : ChartHom d d') (z : ComplexPoints sX)
    (hc : z ∈ chart (sX := sX) c.U) (hd' : z ∈ chart (sX := sX) d'.U)
    (x : c.StalkRing (c.coords ⟨z, hc⟩)) :
    m.transition ⟨z, hd'⟩ (transport c d z hc (chart_mono m.le hd') x) =
      transport c d' z hc hd' x := by
  refine eq_transport_of_isTransport fun e he m₁ m₂ => ?_
  have k := ChartHom.transition_comp_apply m m₂ (m.comp m₂) ⟨z, he⟩
    (transport c d z hc (chart_mono m.le hd') x)
  exact k.symm.trans (isTransport_transport c d z hc _ x e he m₁ (m.comp m₂))

/-- Transport along a coordinate change `m : ChartHom c d` is the transition map of `m`. -/
lemma transport_transition {c d : Chart sX} (m : ChartHom c d) (z : ComplexPoints sX)
    (hd : z ∈ chart (sX := sX) d.U) (x : c.StalkRing (c.coords ⟨z, chart_mono m.le hd⟩)) :
    transport c d z (chart_mono m.le hd) hd x = m.transition ⟨z, hd⟩ x := by
  refine (eq_transport_of_isTransport fun e he m₁ m₂ => ?_).symm
  exact (ChartHom.transition_comp_apply m m₂ m₁ ⟨z, he⟩ x).symm

end Chart

end MMP.Analytic
