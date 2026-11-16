module

public import MMP.AlgebraicGeometry.Semialgebraic.TriangulationLift
public import MMP.AlgebraicGeometry.Semialgebraic.Triangulation
public import MMP.AlgebraicGeometry.Semialgebraic.GoodDirection
public import MMP.AlgebraicGeometry.Semialgebraic.ShearRootBound

/-!
# The triangulation theorem for compact semialgebraic sets

We prove the triangulation theorem (Bochnak–Coste–Roy, Theorem 9.2.1): a compact semialgebraic
set `S ⊆ ℝ^σ` has a standard triangulation compatible with finitely many semialgebraic subsets.
The proof is by induction on the number of coordinates. Write `ℝ^{Option σ} = ℝ^σ × ℝ`. After a
linear change of coordinates `(a, t) ↦ (a + t v, t)` (a good direction), the polynomials defining
`S` and the given subsets, as polynomials in `t`, have nonzero constant leading coefficients, and
so have all their `t`-derivatives. Cover `ℝ^σ` by finitely many connected semialgebraic sets on
which the family of all these polynomials has constant sign pattern, and triangulate the
projection of `S` compatibly with them. Over each open simplex the zeros of the family are
continuous functions of the point, they extend continuously to the closed simplex (constant
leading coefficients bound the zeros), and on each face the extension is one of the zero
functions of the face (the index of the zero is locally constant on the connected open face).
The lifting step (`MMP.exists_isStdTriangulation_of_cells`) then triangulates `S`, and
the change of coordinates carries the triangulation back.

## Main results

* `MMP.stdTriangulable`: compact semialgebraic sets have standard triangulations compatible
  with finitely many semialgebraic subsets.
* `MMP.semialgebraicTriangulation`: the triangulation theorem `MMP.SemialgebraicTriangulation`.
* `MMP.exists_isOpen_contractibleSpace_inter`: closed semialgebraic sets have arbitrarily small
  open neighbourhoods whose trace on the set is contractible.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], Theorem 9.2.1.
-/

@[expose] public section

open Set Filter Topology Polynomial

namespace MMP

/-! ### Constant leading coefficients pass to derivatives -/

section LeadingCoeff

variable {τ : Type*}

/-- A polynomial in `t` over `ℝ[X_τ]` that is zero or has a nonzero constant leading
coefficient. -/
def IsQuasiMonic (G : (MvPolynomial τ ℝ)[X]) : Prop :=
  G = 0 ∨ ∃ c : ℝ, c ≠ 0 ∧ G.leadingCoeff = MvPolynomial.C c

/-- The `t`-derivative of a quasi-monic polynomial is quasi-monic. -/
theorem IsQuasiMonic.derivative {G : (MvPolynomial τ ℝ)[X]} (hG : IsQuasiMonic G) :
    IsQuasiMonic (Polynomial.derivative G) := by
  rcases hG with rfl | ⟨c, hc, hG⟩
  · exact Or.inl (by simp)
  by_cases hd : G.natDegree = 0
  · left
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.derivative_C]
  right
  have hcoeff : (Polynomial.derivative G).coeff (G.natDegree - 1) =
      MvPolynomial.C (c * G.natDegree) := by
    rw [Polynomial.coeff_derivative, Nat.sub_add_cancel (Nat.pos_of_ne_zero hd),
      ← Polynomial.leadingCoeff, hG, map_mul]
    congr 1
    rw [Nat.cast_sub (Nat.pos_of_ne_zero hd), Nat.cast_one, sub_add_cancel]
    simp
  have hc' : c * G.natDegree ≠ 0 := mul_ne_zero hc (Nat.cast_ne_zero.2 hd)
  have hne : MvPolynomial.C (σ := τ) (c * G.natDegree) ≠ 0 := by
    rwa [Ne, MvPolynomial.C_eq_zero]
  have hdeg : (Polynomial.derivative G).natDegree = G.natDegree - 1 :=
    le_antisymm (Polynomial.natDegree_derivative_le G)
      (Polynomial.le_natDegree_of_ne_zero (hcoeff ▸ hne))
  exact ⟨c * G.natDegree, hc', by
    rw [Polynomial.leadingCoeff, hdeg, hcoeff]⟩

/-- Every iterated `t`-derivative of a quasi-monic polynomial is quasi-monic. -/
theorem IsQuasiMonic.iterate_derivative {G : (MvPolynomial τ ℝ)[X]} (hG : IsQuasiMonic G)
    (k : ℕ) : IsQuasiMonic ((⇑Polynomial.derivative)^[k] G) := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.derivative

/-- A nonzero quasi-monic polynomial stays nonzero after specializing the coefficients at any
point `a`. -/
theorem IsQuasiMonic.specAt_ne_zero {G : (MvPolynomial τ ℝ)[X]} (hG : IsQuasiMonic G)
    (hG0 : G ≠ 0) (a : τ → ℝ) : TarskiSeidenberg.specAt a G ≠ 0 := by
  rcases hG with h | ⟨c, hc, hG⟩
  · exact absurd h hG0
  intro h
  have := (natDegree_specAt_of_leadingCoeff hc hG a).2
  rw [h, Polynomial.leadingCoeff_zero] at this
  exact hc this.symm

end LeadingCoeff

/-! ### The index of a zero is locally constant -/

/-- On a preconnected set, a continuous function each of whose values is one of finitely many
continuous, pointwise distinct functions `ξ l` is one of them. -/
theorem eqOn_of_isPreconnected_of_forall_exists_eq {E : Type*} [TopologicalSpace E]
    {U : Set E} (hU : IsPreconnected U) {g : E → ℝ} (hg : ContinuousOn g U) {m : ℕ}
    {ξ : ℕ → E → ℝ} (hξ : ∀ l < m, ContinuousOn (ξ l) U)
    (hsep : ∀ y ∈ U, ∀ l < m, ∀ l' < m, ξ l y = ξ l' y → l = l')
    (hcov : ∀ y ∈ U, ∃ l < m, g y = ξ l y) {y₀ : E} (hy₀ : y₀ ∈ U) {l₀ : ℕ} (hl₀ : l₀ < m)
    (h0 : g y₀ = ξ l₀ y₀) : EqOn g (ξ l₀) U := by
  have hloc : ∀ y ∈ U, ∃ W : Set E, IsOpen W ∧ y ∈ W ∧
      ∀ y' ∈ W ∩ U, ∀ l < m, g y' = ξ l y' → g y = ξ l y := by
    intro y hy
    have hev : ∀ᶠ y' in 𝓝[U] y, ∀ l ∈ {l | l < m}, g y ≠ ξ l y → g y' ≠ ξ l y' := by
      refine (Filter.eventually_all_finite (Set.finite_lt_nat m)).2 fun l hl ↦ ?_
      by_cases hgl : g y = ξ l y
      · exact Filter.Eventually.of_forall fun _ h ↦ absurd hgl h
      · have hc : ContinuousWithinAt (fun y' ↦ g y' - ξ l y') U y :=
          (hg y hy).sub (hξ l hl y hy)
        filter_upwards [hc.eventually_ne (sub_ne_zero.2 hgl)] with y' hy' _ h
        exact hy' (sub_eq_zero.2 h)
    obtain ⟨W, hWo, hyW, hWsub⟩ := mem_nhdsWithin.1 hev
    exact ⟨W, hWo, hyW, fun y' hy' l hl hgl ↦ not_imp_not.1 (hWsub hy' l hl) hgl⟩
  choose! W hWo hyW hWsub using hloc
  by_contra hne
  obtain ⟨y₁, hy₁, hy₁ne⟩ : ∃ y₁ ∈ U, g y₁ ≠ ξ l₀ y₁ := by
    by_contra h
    push Not at h
    exact hne h
  set u := ⋃ y ∈ {y ∈ U | g y = ξ l₀ y}, W y
  set v := ⋃ y ∈ {y ∈ U | g y ≠ ξ l₀ y}, W y
  have hcover : U ⊆ u ∪ v := by
    intro y hy
    by_cases h : g y = ξ l₀ y
    · exact Or.inl (mem_biUnion (x := y) ⟨hy, h⟩ (hyW y hy))
    · exact Or.inr (mem_biUnion (x := y) ⟨hy, h⟩ (hyW y hy))
  obtain ⟨z, hzU, hzu, hzv⟩ := hU u v (isOpen_biUnion fun y hy ↦ hWo y hy.1)
    (isOpen_biUnion fun y hy ↦ hWo y hy.1) hcover
    ⟨y₀, hy₀, mem_biUnion (x := y₀) ⟨hy₀, h0⟩ (hyW y₀ hy₀)⟩
    ⟨y₁, hy₁, mem_biUnion (x := y₁) ⟨hy₁, hy₁ne⟩ (hyW y₁ hy₁)⟩
  obtain ⟨y, ⟨hyU, hyl⟩, hzy⟩ := mem_iUnion₂.1 hzu
  obtain ⟨y', ⟨hy'U, hy'l⟩, hzy'⟩ := mem_iUnion₂.1 hzv
  obtain ⟨l, hl, hgz⟩ := hcov z hzU
  have h1 := hWsub y hyU z ⟨hzy, hzU⟩ l hl hgz
  obtain rfl : l = l₀ := hsep y hyU l hl l₀ hl₀ (h1.symm.trans hyl)
  exact hy'l (hWsub y' hy'U z ⟨hzy', hzU⟩ l hl hgz)

/-! ### Triangulations along maps -/

/-- The composite of a standard triangulation of `S` with a map that is continuous and injective
on `S` is a standard triangulation of the image of `S`. -/
theorem IsStdTriangulation.image {ν σ τ : Type*} [DecidableEq ν] {Δ : Set (Finset ν)}
    {h : (ν → ℝ) → σ → ℝ} {S : Set (σ → ℝ)} (hT : IsStdTriangulation Δ h S)
    {φ : (σ → ℝ) → τ → ℝ} (hφ : ContinuousOn φ S) (hφi : InjOn φ S) :
    IsStdTriangulation Δ (φ ∘ h) (φ '' S) := by
  have hmaps : MapsTo h (stdSpace Δ) S := fun y hy ↦ hT.image_eq ▸ mem_image_of_mem h hy
  refine ⟨hT.nonempty, hT.down_closed, hφ.comp hT.continuousOn hmaps,
    fun y hy y' hy' hyy ↦ hT.injOn hy hy' (hφi (hmaps hy) (hmaps hy') hyy), ?_⟩
  rw [image_comp, hT.image_eq]

/-- Every point of the polyhedron of a standard triangulation lies in the open simplex of one of
its simplices. -/
theorem IsStdTriangulation.exists_mem_openStd {ν σ : Type*} [Fintype ν] [DecidableEq ν]
    {Δ : Set (Finset ν)} {h : (ν → ℝ) → σ → ℝ} {S : Set (σ → ℝ)}
    (hT : IsStdTriangulation Δ h S) {y : ν → ℝ} (hy : y ∈ stdSpace Δ) :
    ∃ t ∈ Δ, y ∈ openStd t := by
  obtain ⟨s, hs, hys⟩ := mem_iUnion₂.1 hy
  rw [← closedStd_eq_convexHull] at hys
  obtain ⟨hts, htne, hyt⟩ := mem_openStd_support hys
  exact ⟨_, hT.down_closed s hs _ hts htne, hyt⟩

/-! ### The shear -/

section Shear

variable {σ : Type*}

/-- The shear `(a, t) ↦ (a + t v, t)` of `ℝ^σ × ℝ`. -/
def shearMap (v : σ → ℝ) (x : Option σ → ℝ) : Option σ → ℝ :=
  optionCons (x ∘ some + x none • v) (x none)

/-- The shear by `-v` is a left inverse of the shear by `v`. -/
@[simp]
theorem shearMap_neg_shearMap (v : σ → ℝ) (x : Option σ → ℝ) :
    shearMap (-v) (shearMap v x) = x := by
  funext o
  rcases o with _ | i
  · rfl
  · simp [shearMap, optionCons]

/-- The shear by `-v` is a right inverse of the shear by `v`. -/
@[simp]
theorem shearMap_shearMap_neg (v : σ → ℝ) (x : Option σ → ℝ) :
    shearMap v (shearMap (-v) x) = x := by
  have := shearMap_neg_shearMap (-v) x
  rwa [neg_neg] at this

/-- The shear is continuous. -/
theorem continuous_shearMap (v : σ → ℝ) : Continuous (shearMap v) := by
  refine continuous_optionCons.comp (Continuous.prodMk ?_ (continuous_apply none))
  exact (continuous_pi fun i ↦ continuous_apply (some i)).add
    ((continuous_apply none).smul continuous_const)

/-- The shear is injective. -/
theorem shearMap_injective (v : σ → ℝ) : Function.Injective (shearMap v) :=
  Function.LeftInverse.injective (shearMap_neg_shearMap v)

/-- The image under the shear of the preimage of a set under the shear is the set itself. -/
theorem image_shearMap_preimage (v : σ → ℝ) (S : Set (Option σ → ℝ)) :
    shearMap v '' (shearMap v ⁻¹' S) = S :=
  image_preimage_eq S (Function.RightInverse.surjective (shearMap_shearMap_neg v))

/-- The shear is the polynomial map `(a, t) ↦ (a + t v, t)`. -/
theorem shearMap_eq_polynomialMap [Finite σ] (v : σ → ℝ) :
    shearMap v = IsSemialgebraic.polynomialMap (fun o : Option σ ↦
      o.elim (MvPolynomial.X none) fun i ↦
        MvPolynomial.X (some i) + MvPolynomial.C (v i) * MvPolynomial.X none) := by
  funext x o
  rcases o with _ | i
  · simp [shearMap, optionCons, IsSemialgebraic.polynomialMap]
  · simp [shearMap, optionCons, IsSemialgebraic.polynomialMap, mul_comm]

/-- The preimage of a semialgebraic set under the shear is semialgebraic. -/
theorem IsSemialgebraic.preimage_shearMap [Finite σ] (v : σ → ℝ) {S : Set (Option σ → ℝ)}
    (hS : IsSemialgebraic S) : IsSemialgebraic (shearMap v ⁻¹' S) := by
  rw [shearMap_eq_polynomialMap]
  exact IsSemialgebraic.preimage_polynomialMap _ hS

end Shear

/-! ### Zero functions over a triangulated base -/

section RootData

open TarskiSeidenberg

/-- The barycentre of a nonempty standard simplex lies in its open simplex. -/
theorem baryStd_mem_openStd {ν : Type*} [Fintype ν] [DecidableEq ν] {s : Finset ν}
    (hs : s.Nonempty) : baryStd s ∈ openStd s := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  exact ⟨fun u hu ↦ by simp [baryStd, hu, hc], (baryStd_mem s hs).1, (baryStd_mem s hs).2⟩

/-- Every zero of a finite family of real polynomials is its `l`-th smallest zero for some
`l` less than the number of zeros. -/
theorem exists_familyRootsNth_eq {ι : Type*} [Fintype ι] {f : ι → ℝ[X]} {z : ℝ}
    (hz : z ∈ familyRoots f) : ∃ l < (familyRoots f).card, familyRootsNth f l = z := by
  obtain ⟨i, hi⟩ : z ∈ Set.range ((familyRoots f).orderEmbOfFin rfl) := by
    rwa [Finset.range_orderEmbOfFin]
  exact ⟨i, i.2, by rw [familyRootsNth_eq_orderEmbOfFin rfl i, hi]⟩

/-- A point below a point of the lowest band of a finite family lies in the lowest band. -/
theorem InFamilyRootsBand.zero_of_lt {ι : Type*} [Fintype ι] {f : ι → ℝ[X]} {t t' : ℝ}
    (ht : InFamilyRootsBand f 0 t) (htt' : t' < t) : InFamilyRootsBand f 0 t' := by
  have hlt : ∀ z ∈ familyRoots f, ¬ z < t := fun z hz ↦
    Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 ht.2) hz
  refine ⟨fun h ↦ hlt t' h htt', ?_⟩
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun z hz hzt ↦ hlt z hz (hzt.trans htt')

/-- A point above a point of the highest band of a finite family lies in the highest band. -/
theorem InFamilyRootsBand.card_of_lt {ι : Type*} [Fintype ι] {f : ι → ℝ[X]} {t t' : ℝ}
    (ht : InFamilyRootsBand f (familyRoots f).card t) (htt' : t < t') :
    InFamilyRootsBand f (familyRoots f).card t' := by
  have hlt : ∀ z ∈ familyRoots f, z < t := fun z hz ↦ by
    rw [← Finset.eq_of_subset_of_card_le (Finset.filter_subset (· < t) _) ht.2.ge] at hz
    exact (Finset.mem_filter.1 hz).2
  refine ⟨fun h ↦ lt_asymm (hlt t' h) htt', ?_⟩
  rw [Finset.filter_true_of_mem fun z hz ↦ (hlt z hz).trans htt']

/-- **The zero functions over a triangulated base.** Let `P` be a finite family of polynomials
in `t` over `ℝ[X_σ]`, closed under `∂/∂t`, each zero or with a nonzero constant leading
coefficient, and `h₀` a standard triangulation whose open simplices map into sets of constant
sign pattern of `P`. Then over each simplex `s` the zeros `ζ s 0 < ⋯ < ζ s (n s - 1)` of
`P(h₀ y, ·)` are continuous on the open simplex, extend continuously to the closed simplex, and
restrict on the open simplex of each face to zero functions of the face. -/
theorem exists_rootData {σ ν ι₂ : Type*} [Fintype σ] [Fintype ν] [DecidableEq ν] [Fintype ι₂]
    {P : ι₂ → (MvPolynomial σ ℝ)[X]} (hder : ∀ i, ∃ j, P j = Polynomial.derivative (P i))
    (hqm : ∀ i, IsQuasiMonic (P i)) {Δ : Set (Finset ν)} {h₀ : (ν → ℝ) → σ → ℝ}
    {B : Set (σ → ℝ)} (hT : IsStdTriangulation Δ h₀ B)
    (hpat : ∀ s ∈ Δ, ∀ y ∈ openStd s, ∀ y' ∈ openStd s,
      SameSignPattern (fun i ↦ specAt (h₀ y) (P i)) (fun i ↦ specAt (h₀ y') (P i))) :
    ∃ (n : Finset ν → ℕ) (ζ : Finset ν → ℕ → (ν → ℝ) → ℝ),
      (∀ s ∈ Δ, ∀ y ∈ openStd s, (familyRoots fun i ↦ specAt (h₀ y) (P i)).card = n s) ∧
      (∀ s ∈ Δ, ∀ j < n s, ∀ y ∈ openStd s,
        ζ s j y = familyRootsNth (fun i ↦ specAt (h₀ y) (P i)) j) ∧
      (∀ s ∈ Δ, ∀ j < n s, ContinuousOn (ζ s j) (closedStd s)) ∧
      (∀ s ∈ Δ, ∀ y ∈ openStd s, ∀ j j', j < j' → j' < n s → ζ s j y < ζ s j' y) ∧
      (∀ s ∈ Δ, ∀ t ∈ Δ, t ⊆ s → ∀ j < n s, ∃ l < n t, EqOn (ζ s j) (ζ t l) (openStd t)) := by
  classical
  set F : (σ → ℝ) → ι₂ → ℝ[X] := fun a i ↦ specAt a (P i)
  have hh₀ : ∀ s ∈ Δ, ContinuousOn h₀ (closedStd s) := fun s hs ↦
    hT.continuousOn.mono (closedStd_subset_stdSpace hs)
  have hder' : ∀ i, ∃ j, ∀ a, specAt a (P j) = Polynomial.derivative (specAt a (P i)) := fun i ↦ by
    obtain ⟨j, hj⟩ := hder i
    exact ⟨j, fun a ↦ by simp only [hj, specAt_derivative]⟩
  set n : Finset ν → ℕ := fun s ↦ (familyRoots (F (h₀ (baryStd s)))).card
  have hn : ∀ s ∈ Δ, ∀ y ∈ openStd s, (familyRoots (F (h₀ y))).card = n s := fun s hs y hy ↦
    (hpat s hs y hy _ (baryStd_mem_openStd (hT.nonempty s hs))).card_familyRoots_eq
  have hex : ∀ s ∈ Δ, ∀ j < n s, ∃ (g : (ν → ℝ) → ℝ) (i : ι₂), ContinuousOn g (closedStd s) ∧
      EqOn g (fun y ↦ familyRootsNth (F (h₀ y)) j) (openStd s) ∧ P i ≠ 0 ∧
      ∀ y ∈ closedStd s, (specAt (h₀ y) (P i)).eval (g y) = 0 := by
    intro s hs j hj
    have hs' := hT.nonempty s hs
    have hb := baryStd_mem_openStd hs'
    obtain ⟨i, hi0, hiroot⟩ := mem_familyRoots.1 (familyRootsNth_mem (f := F (h₀ (baryStd s))) hj)
    have hPi : P i ≠ 0 := fun h ↦ hi0 (by simp [F, h])
    obtain ⟨c, hc, hlc⟩ := (hqm i).resolve_left hPi
    have hξ : ContinuousOn (fun y ↦ familyRootsNth (F (h₀ y)) j) (openStd s) := by
      have hC : ∀ a ∈ h₀ '' openStd s, ∀ b ∈ h₀ '' openStd s,
          SameSignPattern (fun i ↦ specAt a (P i)) (fun i ↦ specAt b (P i)) := by
        rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
        exact hpat s hs y hy y' hy'
      exact (continuousOn_familyRootsNth (F := fun i a ↦ specAt a (P i)) hC
        (fun i x ↦ continuous_eval_specAt (P i) x) hder' j).comp
        ((hh₀ s hs).mono (openStd_subset_closedStd s)) (mapsTo_image _ _)
    have hξF : ∀ y ∈ openStd s, (specAt (h₀ y) (P i)).eval (familyRootsNth (F (h₀ y)) j) = 0 := by
      intro y hy
      have := (hpat s hs _ hb y hy).sign_eval_familyRootsNth i hj
      rw [show (F (h₀ (baryStd s)) i).eval (familyRootsNth (F (h₀ (baryStd s))) j) = 0 from hiroot,
        sign_zero] at this
      exact sign_eq_zero_iff.1 this.symm
    have hh := hh₀ s hs
    rw [closedStd_eq_convexHull] at hh
    rw [openStd_eq_openSimplex] at hξ hξF
    obtain ⟨g, hg, hgξ, hgF⟩ := exists_continuousOn_convexHull_of_specAt hc hlc
      (hs'.map (f := stdVertex ν)) hh hξ hξF
    refine ⟨g, i, ?_, ?_, hPi, ?_⟩
    · rwa [closedStd_eq_convexHull]
    · rwa [openStd_eq_openSimplex]
    · rwa [closedStd_eq_convexHull]
  choose! ζ ii hζc hζe hii hζr using hex
  have hmono : ∀ s ∈ Δ, ∀ y ∈ openStd s, ∀ j j', j < j' → j' < n s → ζ s j y < ζ s j' y := by
    intro s hs y hy j j' hjj' hj'
    rw [hζe s hs j (hjj'.trans hj') hy, hζe s hs j' hj' hy]
    exact familyRootsNth_strictMonoOn (by simp only [mem_setOf_eq, hn s hs y hy]; omega)
      (by simp only [mem_setOf_eq, hn s hs y hy]; omega) hjj'
  refine ⟨n, ζ, hn, fun s hs j hj y hy ↦ hζe s hs j hj hy, hζc, hmono, ?_⟩
  intro s hs t ht hts j hj
  have hU : IsPreconnected (openStd t) := by
    rw [openStd_eq_openSimplex]
    exact (convex_openSimplex _).isPreconnected
  have hsub : openStd t ⊆ closedStd s :=
    (openStd_subset_closedStd t).trans (closedStd_mono hts)
  have hcov : ∀ y ∈ openStd t, ∃ l < n t, ζ s j y = ζ t l y := by
    intro y hy
    have hr : ζ s j y ∈ familyRoots (F (h₀ y)) := mem_familyRoots.2
      ⟨ii s hs j hj, (hqm _).specAt_ne_zero (hii s hs j hj) _, hζr s hs j hj y (hsub hy)⟩
    obtain ⟨l, hl, hle⟩ := exists_familyRootsNth_eq hr
    rw [hn t ht y hy] at hl
    exact ⟨l, hl, ((hζe t ht l hl hy).trans hle).symm⟩
  have hb := baryStd_mem_openStd (hT.nonempty t ht)
  obtain ⟨l₀, hl₀, h0⟩ := hcov _ hb
  refine ⟨l₀, hl₀, eqOn_of_isPreconnected_of_forall_exists_eq hU ((hζc s hs j hj).mono hsub)
    (fun l hl ↦ (hζc t ht l hl).mono (openStd_subset_closedStd t)) (fun y hy l hl l' hl' h ↦ ?_)
    hcov hb hl₀ h0⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact (hmono t ht y hy l l' h' hl').ne h
  · exact (hmono t ht y hy l' l h' hl).ne' h

/-- Let `S ⊆ ℝ^σ × ℝ` be a set bounded in the last coordinate, which contains, with each of its
points, the whole band over the base point containing it. Then every point of `S` over the base
of a standard triangulation lies on the graph of a zero function or in a bounded band between two
consecutive zero functions. -/
theorem exists_mem_graphCell_or_bandCell {σ ν ι : Type*} [Fintype ν] [DecidableEq ν]
    [Fintype ι] {Δ : Set (Finset ν)} {h₀ : (ν → ℝ) → σ → ℝ} {B : Set (σ → ℝ)}
    (hT : IsStdTriangulation Δ h₀ B) {F : (σ → ℝ) → ι → ℝ[X]} {n : Finset ν → ℕ}
    {ζ : Finset ν → ℕ → (ν → ℝ) → ℝ}
    (hn : ∀ s ∈ Δ, ∀ y ∈ openStd s, (familyRoots (F (h₀ y))).card = n s)
    (hζ : ∀ s ∈ Δ, ∀ j < n s, ∀ y ∈ openStd s, ζ s j y = familyRootsNth (F (h₀ y)) j)
    {S : Set (Option σ → ℝ)} {R : ℝ} (hR : ∀ z ∈ S, |z none| ≤ R)
    (hband : ∀ x ∈ S, ∀ j t, InFamilyRootsBand (F (x ∘ some)) j (x none) →
      InFamilyRootsBand (F (x ∘ some)) j t → optionCons (x ∘ some) t ∈ S)
    {x : Option σ → ℝ} (hx : x ∈ S) (hxB : x ∘ some ∈ B) :
    ∃ s ∈ Δ, (∃ j < n s, x ∈ graphCell h₀ (ζ s j) s) ∨
      ∃ j, j + 1 < n s ∧ x ∈ bandCell h₀ (ζ s j) (ζ s (j + 1)) s := by
  rw [← hT.image_eq] at hxB
  obtain ⟨y₀, hy₀, hya⟩ := hxB
  obtain ⟨s, hs, hyt⟩ := hT.exists_mem_openStd hy₀
  refine ⟨s, hs, ?_⟩
  have hx_eq : x = optionCons (h₀ y₀) (x none) := by
    rw [hya]
    exact (optionCons_eta x).symm
  have hin : ∀ j t, InFamilyRootsBand (F (h₀ y₀)) j (x none) →
      InFamilyRootsBand (F (h₀ y₀)) j t → optionCons (h₀ y₀) t ∈ S := by
    rw [hya]
    exact hband x hx
  set τ := x none
  have hnc := hn s hs y₀ hyt
  by_cases hroot : τ ∈ familyRoots (F (h₀ y₀))
  · obtain ⟨j, hj, hjτ⟩ := exists_familyRootsNth_eq hroot
    rw [hnc] at hj
    refine Or.inl ⟨j, hj, y₀, hyt, ?_⟩
    change optionCons (h₀ y₀) (ζ s j y₀) = x
    rw [hx_eq, hζ s hs j hj y₀ hyt, hjτ]
  obtain ⟨m, hm⟩ : ∃ m, InFamilyRootsBand (F (h₀ y₀)) m τ := ⟨_, hroot, rfl⟩
  have hm_le : m ≤ n s := by
    rw [← hnc, ← hm.2]
    exact Finset.card_filter_le _ _
  cases m with
  | zero =>
    exfalso
    have := hR _ (hin 0 _ hm (hm.zero_of_lt (t' := min τ (-R) - 1)
      (by linarith [min_le_left τ (-R)])))
    simp only [optionCons_none] at this
    linarith [min_le_right τ (-R), (abs_le.1 this).1]
  | succ j =>
    by_cases hmn : j + 1 = n s
    · exfalso
      rw [hmn, ← hnc] at hm
      have := hR _ (hin _ _ hm (hm.card_of_lt (t' := max τ R + 1)
        (by linarith [le_max_left τ R])))
      simp only [optionCons_none] at this
      linarith [le_max_right τ R, (abs_le.1 this).2]
    have hj1 : j + 1 < n s := lt_of_le_of_ne hm_le hmn
    set ξ := familyRootsNth (F (h₀ y₀))
    have hξlt : ξ j < ξ (j + 1) := familyRootsNth_strictMonoOn
      (by simp only [mem_setOf_eq, hnc]; omega) (by simp only [mem_setOf_eq, hnc]; omega)
      (Nat.lt_succ_self j)
    have hb₀ : InFamilyRootsBand (F (h₀ y₀)) (j + 1) ((ξ j + ξ (j + 1)) / 2) :=
      inFamilyRootsBand_of_lt (by omega) (fun _ ↦ by rw [Nat.add_sub_cancel]; linarith)
        (fun _ ↦ by linarith)
    have hmemj : ξ j ∈ familyRoots (F (h₀ y₀)) := familyRootsNth_mem (by omega)
    have hmemj1 : ξ (j + 1) ∈ familyRoots (F (h₀ y₀)) := familyRootsNth_mem (by omega)
    refine Or.inr ⟨j, hj1, y₀, hyt, τ, ?_, ?_, hx_eq.symm⟩
    · rw [hζ s hs j (by omega) y₀ hyt]
      exact (hb₀.lt_iff_lt hm hmemj).1 (by linarith)
    · rw [hζ s hs (j + 1) hj1 y₀ hyt]
      have : ¬ ξ (j + 1) < τ := fun h ↦ absurd ((hb₀.lt_iff_lt hm hmemj1).2 h) (by linarith)
      exact lt_of_le_of_ne (not_lt.1 this) fun h ↦ hroot (h ▸ hmemj1)

end RootData

/-! ### The induction -/

section Induction

open TarskiSeidenberg

/-- Compact semialgebraic subsets of `ℝ^σ` have standard triangulations compatible with
finitely many semialgebraic subsets. -/
def StdTriangulable (σ : Type) : Prop :=
  ∀ (S : Set (σ → ℝ)) (ι : Type) [Finite ι] (A : ι → Set (σ → ℝ)), IsCompact S →
    IsSemialgebraic S → (∀ j, IsSemialgebraic (A j)) → (∀ j, A j ⊆ S) →
    ∃ (ν : Type) (_ : Fintype ν) (_ : DecidableEq ν) (Δ : Set (Finset ν))
      (h : (ν → ℝ) → σ → ℝ), IsStdTriangulation Δ h S ∧
      ∀ j, ∀ s ∈ Δ, h '' openSimplex (s.map (stdVertex ν)) ⊆ A j ∨
        Disjoint (h '' openSimplex (s.map (stdVertex ν))) (A j)

/-- Standard triangulability is invariant under a bijection of the coordinate index types. -/
theorem stdTriangulable_of_equiv {α β : Type} (e : α ≃ β) (H : StdTriangulable α) :
    StdTriangulable β := by
  intro S ι _ A hSc hSs hAs hAS
  set φ : (α → ℝ) → β → ℝ := fun x ↦ x ∘ e.symm
  have hφ : Continuous φ := continuous_pi fun b ↦ continuous_apply _
  have hφi : Function.Injective φ := fun x x' h ↦ by
    funext a
    simpa [φ] using congrFun h (e a)
  have hpre : ∀ T : Set (β → ℝ), φ '' (φ ⁻¹' T) = T := fun T ↦ by
    refine image_preimage_eq T fun y ↦ ⟨y ∘ e, ?_⟩
    funext b
    simp [φ]
  have hSc' : IsCompact (φ ⁻¹' S) := by
    rw [← image_eq_preimage_of_inverse (f := fun y : β → ℝ ↦ y ∘ e) (g := φ)
      (fun y ↦ by funext b; simp [φ]) (fun y ↦ by funext b; simp [φ])]
    exact hSc.image (continuous_pi fun a ↦ continuous_apply _)
  obtain ⟨ν, _, _, Δ, h, hT, hcomp⟩ := H (φ ⁻¹' S) ι (fun j ↦ φ ⁻¹' A j) hSc'
    (IsSemialgebraic.preimage_comp (R := ℝ) e.symm hSs)
    (fun j ↦ IsSemialgebraic.preimage_comp (R := ℝ) e.symm (hAs j))
    (fun j ↦ preimage_mono (hAS j))
  refine ⟨ν, inferInstance, inferInstance, Δ, φ ∘ h, ?_, fun j s hs ↦ ?_⟩
  · simpa [hpre] using hT.image hφ.continuousOn hφi.injOn
  · rw [image_comp]
    exact (hcomp j s hs).imp image_subset_iff.2 disjoint_image_left.2

/-- Compact semialgebraic subsets of `ℝ^0` are standard triangulable. -/
theorem stdTriangulable_pEmpty : StdTriangulable PEmpty := by
  intro S ι _ A hSc hSs hAs hAS
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨Empty, inferInstance, inferInstance, ∅, fun _ p ↦ p.elim, ⟨fun _ h ↦ h.elim,
      fun _ h ↦ h.elim, by simp [stdSpace], by simp [stdSpace], by simp [stdSpace]⟩,
      fun _ _ h ↦ h.elim⟩
  · have hS : S = {x₀} := Set.eq_singleton_iff_unique_mem.2
      ⟨hx₀, fun x _ ↦ Subsingleton.elim x x₀⟩
    have hsp : stdSpace ({{()}} : Set (Finset Unit)) = {Pi.single () 1} := by
      ext y
      simp only [stdSpace, mem_singleton_iff, iUnion_iUnion_eq_left, ← closedStd_eq_convexHull]
      constructor
      · rintro ⟨-, h1, -⟩
        funext u
        simpa using h1
      · rintro rfl
        exact ⟨fun u ↦ by simp, by simp, fun u hu ↦ absurd (Finset.mem_singleton_self u) hu⟩
    refine ⟨Unit, inferInstance, inferInstance, {{()}}, fun _ ↦ x₀, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro s hs
      rw [mem_singleton_iff.1 hs]
      exact Finset.singleton_nonempty _
    · intro s hs t hts htne
      rw [mem_singleton_iff.1 hs] at hts
      exact mem_singleton_iff.2 ((Finset.Nonempty.subset_singleton_iff htne).1 hts)
    · exact continuousOn_const
    · rw [hsp]
      exact injOn_singleton _ _
    · rw [hsp, image_singleton, hS]
    · intro j s hs
      rw [mem_singleton_iff.1 hs]
      have hsub : (fun _ ↦ x₀) '' openSimplex (({()} : Finset Unit).map (stdVertex Unit)) ⊆ {x₀} :=
        fun _ ⟨_, _, h⟩ ↦ h.symm ▸ rfl
      by_cases hj : x₀ ∈ A j
      · exact Or.inl (hsub.trans (singleton_subset_iff.2 hj))
      · refine Or.inr (Set.disjoint_left.2 fun z hz hzA ↦ hj ?_)
        rwa [← mem_singleton_iff.1 (hsub hz)]

/-- The projection to `ℝ^σ` of a compact semialgebraic `S ⊆ ℝ^σ × ℝ` has a standard
triangulation over whose open simplices a finite family `P` has constant sign pattern. -/
theorem exists_isStdTriangulation_sameSignPattern {σ ι₂ : Type} [Fintype ι₂]
    (IH : StdTriangulable σ) (P : ι₂ → (MvPolynomial σ ℝ)[X]) {S : Set (Option σ → ℝ)}
    (hSc : IsCompact S) (hSs : IsSemialgebraic S) :
    ∃ (ν : Type) (_ : Fintype ν) (_ : DecidableEq ν) (Δ : Set (Finset ν))
      (h₀ : (ν → ℝ) → σ → ℝ) (B : Set (σ → ℝ)), IsStdTriangulation Δ h₀ B ∧
      (∀ x ∈ S, x ∘ some ∈ B) ∧ ∀ s ∈ Δ, ∀ y ∈ openStd s, ∀ y' ∈ openStd s,
        SameSignPattern (fun i ↦ specAt (h₀ y) (P i)) (fun i ↦ specAt (h₀ y') (P i)) := by
  obtain ⟨κc, _, C, hC, hCU, hCP⟩ := hasSignPatternCover P (IsSemialgebraic.univ (σ := σ))
  set B : Set (σ → ℝ) := {a | ∃ t : ℝ, (fun o ↦ o.elim t a) ∈ S}
  have hBs : IsSemialgebraic B := IsSemialgebraic.projection hSs
  have hBeq : B = (fun x : Option σ → ℝ ↦ x ∘ some) '' S := by
    ext a
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨_, ht, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x none, ?_⟩
      convert hx using 1
      exact optionCons_eta x
  obtain ⟨ν, _, _, Δ, h₀, hT, hcomp⟩ := IH B κc (fun k ↦ C k ∩ B)
    (hBeq ▸ hSc.image (continuous_pi fun i ↦ continuous_apply _)) hBs
    (fun k ↦ (hC k).inter hBs) (fun k ↦ inter_subset_right)
  refine ⟨ν, inferInstance, inferInstance, Δ, h₀, B, hT, fun x hx ↦ hBeq ▸ ⟨x, hx, rfl⟩, ?_⟩
  intro s hs y hy y' hy'
  have hyB : h₀ y ∈ B := hT.image_eq ▸ mem_image_of_mem h₀
    (closedStd_subset_stdSpace hs (openStd_subset_closedStd s hy))
  obtain ⟨k, hk⟩ := mem_iUnion.1 (hCU.symm ▸ mem_univ (h₀ y) : h₀ y ∈ ⋃ k, C k)
  rw [openStd_eq_openSimplex] at hy hy'
  rcases hcomp k s hs with h | h
  · exact hCP k _ (h ⟨y, hy, rfl⟩).1 _ (h ⟨y', hy', rfl⟩).1
  · exact absurd ⟨hk, hyB⟩ (Set.disjoint_left.1 h ⟨y, hy, rfl⟩)

/-- **The lifting step along a family of quasi-monic polynomials.** Let `P` be closed under
`∂/∂t` and quasi-monic, `h₀` a standard triangulation of `B` over whose open simplices `P` has
constant sign pattern, and `T` a family of sets in `ℝ^σ × ℝ` whose membership depends only on
the signs of `P`, with `T none` compact and lying over `B`. Then `T none` has a standard
triangulation compatible with every `T (some i)`. -/
theorem exists_isStdTriangulation_of_forall_sign_eq {σ ν ι₂ : Type} [Fintype σ] [Fintype ν]
    [DecidableEq ν] [Fintype ι₂] {P : ι₂ → (MvPolynomial σ ℝ)[X]}
    (hder : ∀ i, ∃ j, P j = Polynomial.derivative (P i)) (hqm : ∀ i, IsQuasiMonic (P i))
    {Δ : Set (Finset ν)} {h₀ : (ν → ℝ) → σ → ℝ} {B : Set (σ → ℝ)}
    (hT : IsStdTriangulation Δ h₀ B)
    (hpat : ∀ s ∈ Δ, ∀ y ∈ openStd s, ∀ y' ∈ openStd s,
      SameSignPattern (fun i ↦ specAt (h₀ y) (P i)) (fun i ↦ specAt (h₀ y') (P i)))
    {ι : Type*} {T : Option ι → Set (Option σ → ℝ)}
    (hmem : ∀ l (x y : Option σ → ℝ),
      (∀ i, SignType.sign ((specAt (x ∘ some) (P i)).eval (x none)) =
        SignType.sign ((specAt (y ∘ some) (P i)).eval (y none))) → x ∈ T l → y ∈ T l)
    (hc : IsCompact (T none)) (hB : ∀ x ∈ T none, x ∘ some ∈ B) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (Δ' : Set (Finset κ))
      (h' : (κ → ℝ) → Option σ → ℝ), IsStdTriangulation Δ' h' (T none) ∧
      ∀ i, ∀ c ∈ Δ', h' '' openSimplex (c.map (stdVertex κ)) ⊆ T (some i) ∨
        Disjoint (h' '' openSimplex (c.map (stdVertex κ))) (T (some i)) := by
  obtain ⟨n, ζ, hn, hζ, hcont, hmono, hface⟩ := exists_rootData hder hqm hT hpat
  set F : (σ → ℝ) → ι₂ → ℝ[X] := fun a i ↦ specAt a (P i)
  have hgraph : ∀ s ∈ Δ, ∀ j < n s, ∀ y ∈ openStd s, ∀ y' ∈ openStd s, ∀ i,
      SignType.sign ((F (h₀ y) i).eval (ζ s j y)) =
        SignType.sign ((F (h₀ y') i).eval (ζ s j y')) := by
    intro s hs j hj y hy y' hy' i
    rw [hζ s hs j hj y hy, hζ s hs j hj y' hy']
    exact (hpat s hs y hy y' hy').sign_eval_familyRootsNth i (by rwa [hn s hs y hy])
  have hband : ∀ s ∈ Δ, ∀ j, j + 1 < n s → ∀ y ∈ openStd s, ∀ t, ζ s j y < t →
      t < ζ s (j + 1) y → InFamilyRootsBand (F (h₀ y)) (j + 1) t := by
    intro s hs j hj y hy t h1 h2
    refine inFamilyRootsBand_of_lt (by rw [hn s hs y hy]; omega) (fun _ ↦ ?_) (fun _ ↦ ?_)
    · rwa [Nat.add_sub_cancel, ← hζ s hs j (by omega) y hy]
    · rwa [← hζ s hs (j + 1) hj y hy]
  have hcellg : ∀ l, ∀ s ∈ Δ, ∀ j < n s, ∀ x ∈ graphCell h₀ (ζ s j) s,
      ∀ x' ∈ graphCell h₀ (ζ s j) s, x ∈ T l → x' ∈ T l := by
    rintro l s hs j hj _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hx
    exact hmem l _ _ (hgraph s hs j hj y hy y' hy') hx
  have hcellb : ∀ l, ∀ s ∈ Δ, ∀ j, j + 1 < n s → ∀ x ∈ bandCell h₀ (ζ s j) (ζ s (j + 1)) s,
      ∀ x' ∈ bandCell h₀ (ζ s j) (ζ s (j + 1)) s, x ∈ T l → x' ∈ T l := by
    rintro l s hs j hj _ ⟨y, hy, t, h1, h2, rfl⟩ _ ⟨y', hy', t', h1', h2', rfl⟩ hx
    exact hmem l _ _ (fun i ↦ (hpat s hs y hy y' hy').sign_eval_of_inFamilyRootsBand
      (hband s hs j hj y hy t h1 h2) (hband s hs j hj y' hy' t' h1' h2') i) hx
  obtain ⟨R, hR⟩ : ∃ R, ∀ z ∈ T none, |z none| ≤ R := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1
      ((hc.image (continuous_apply none)).isBounded)
    exact ⟨R, fun z hz ↦ by simpa using hR _ ⟨z, hz, rfl⟩⟩
  exact exists_isStdTriangulation_of_cells hT n ζ hcont hmono hface hc.isClosed
    (fun x hx ↦ exists_mem_graphCell_or_bandCell hT (F := F) hn hζ hR
      (fun x hx _ t hb hb' ↦ hmem none x (optionCons (x ∘ some) t)
        (fun i ↦ hb.sign_eval_eq hb' i) hx) hx (hB x hx))
    (fun s hs j hj ⟨x, hxg, hxS⟩ x' hx' ↦ hcellg none s hs j hj x hxg x' hx' hxS)
    (fun s hs j hj ⟨x, hxb, hxS⟩ x' hx' ↦ hcellb none s hs j hj x hxb x' hx' hxS)
    (fun i ↦ T (some i))
    (fun i s hs j hj ↦ subset_or_disjoint_of_forall_mem_iff fun x hx x' hx' ↦
      hcellg (some i) s hs j hj x hx x' hx')
    (fun i s hs j hj ↦ subset_or_disjoint_of_forall_mem_iff fun x hx x' hx' ↦
      hcellb (some i) s hs j hj x hx x' hx')

/-- **The induction step of the triangulation theorem**: if compact semialgebraic subsets of
`ℝ^σ` are standard triangulable compatibly with finitely many semialgebraic subsets, then so
are those of `ℝ^{Option σ} = ℝ^σ × ℝ`. -/
theorem stdTriangulable_option {σ : Type} [Finite σ] (IH : StdTriangulable σ) :
    StdTriangulable (Option σ) := by
  classical
  intro S ι _ A hSc hSs hAs hAS
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite ι
  -- the sets and their sign conditions
  let T : Option ι → Set (Option σ → ℝ) := fun l ↦ l.elim S A
  have hTs : ∀ l, IsSemialgebraic (T l) := Option.forall.2 ⟨hSs, hAs⟩
  choose κ hκ Q E hQ using fun l ↦ (hTs l).exists_signConditions
  -- a good direction
  obtain ⟨v, hv⟩ := exists_shearPolynomial_leadingCoeff_forall (K := ℝ) (σ := σ)
    (Finset.univ.filter fun p : (Σ l, κ l) ↦ Q p.1 p.2 ≠ 0) (f := fun p ↦ Q p.1 p.2)
    (fun p hp ↦ (Finset.mem_filter.1 hp).2)
  set P₀ : (Σ l, κ l) → (MvPolynomial σ ℝ)[X] := fun p ↦ shearPolynomial v (Q p.1 p.2)
  have hP₀ : ∀ p, IsQuasiMonic (P₀ p) := fun p ↦ by
    by_cases hp : Q p.1 p.2 = 0
    · exact Or.inl (by simp [P₀, hp])
    · exact Or.inr (hv p (by simp [hp]))
  set P := derivativeClosure P₀
  have hqm : ∀ i, IsQuasiMonic (P i) := fun i ↦ (hP₀ i.1).iterate_derivative i.2
  -- membership in the sheared sets only depends on the signs of `P`
  have hmem : ∀ l (x y : Option σ → ℝ),
      (∀ i, SignType.sign ((specAt (x ∘ some) (P i)).eval (x none)) =
        SignType.sign ((specAt (y ∘ some) (P i)).eval (y none))) →
      x ∈ shearMap v ⁻¹' T l → y ∈ shearMap v ⁻¹' T l := by
    intro l x y hxy hx
    have hev : ∀ (z : Option σ → ℝ) m, MvPolynomial.eval (shearMap v z) (Q l m) =
        (specAt (z ∘ some) (P (⟨l, m⟩, 0))).eval (z none) := fun z m ↦ by
      rw [show P (⟨l, m⟩, 0) = P₀ ⟨l, m⟩ from rfl, eval_specAt_shearPolynomial]
      rfl
    simp only [mem_preimage] at hx ⊢
    rw [hQ l] at hx ⊢
    simp only [mem_setOf_eq] at hx ⊢
    convert hx using 2 with m
    rw [hev, hev]
    exact (hxy _).symm
  -- the sheared set
  set S' := shearMap v ⁻¹' S
  have hS'eq : S' = shearMap (-v) '' S :=
    (congrFun (image_eq_preimage_of_inverse (shearMap_shearMap_neg v)
      (shearMap_neg_shearMap v)) S).symm
  have hS'c : IsCompact S' := hS'eq ▸ hSc.image (continuous_shearMap _)
  obtain ⟨ν, _, _, Δ, h₀, B, hT, hB, hpat⟩ := exists_isStdTriangulation_sameSignPattern IH P
    hS'c (IsSemialgebraic.preimage_shearMap v hSs)
  obtain ⟨κ', _, _, Δ', h', hT', hcomp'⟩ := exists_isStdTriangulation_of_forall_sign_eq
    (derivativeClosure_derivative_closed P₀) hqm hT hpat (T := fun l ↦ shearMap v ⁻¹' T l)
    hmem hS'c hB
  -- back along the shear
  refine ⟨κ', inferInstance, inferInstance, Δ', shearMap v ∘ h', ?_, fun j c hc ↦ ?_⟩
  · have := hT'.image (continuous_shearMap v).continuousOn (shearMap_injective v).injOn
    rwa [image_shearMap_preimage] at this
  · rw [image_comp]
    exact (hcomp' j c hc).imp image_subset_iff.2 disjoint_image_left.2

/-- **The triangulation theorem, standard form.** A compact semialgebraic `S ⊆ ℝ^σ` has a
standard triangulation compatible with finitely many semialgebraic subsets. -/
theorem stdTriangulable (σ : Type) [Finite σ] : StdTriangulable σ :=
  Finite.induction_empty_option (P := StdTriangulable) stdTriangulable_of_equiv
    stdTriangulable_pEmpty
    (fun h ↦ stdTriangulable_option h) σ

/-- **The triangulation theorem for compact semialgebraic sets** (Bochnak–Coste–Roy, Theorem
9.2.1). -/
theorem semialgebraicTriangulation : SemialgebraicTriangulation := by
  intro σ _ S ι _ A hSc hSs hAs hAS
  obtain ⟨ν, _, _, Δ, h, hT, hcomp⟩ := stdTriangulable σ S ι A hSc hSs hAs hAS
  exact hT.exists_simplicialComplex hcomp

end Induction

/-! ### Open contractible neighbourhoods -/

section OpenStar

/-- The vertex `Pi.single u 1` of the standard simplex of `t` lies in its closed simplex when
`u ∈ t`. -/
theorem single_mem_closedStd {ν : Type*} [Fintype ν] [DecidableEq ν] {t : Finset ν} {u : ν}
    (hu : u ∈ t) : Pi.single u (1 : ℝ) ∈ closedStd t := by
  refine ⟨fun v ↦ by rw [Pi.single_apply]; split_ifs <;> norm_num, by simp, fun v hv ↦ ?_⟩
  rw [Pi.single_apply, if_neg]
  rintro rfl
  exact hv hu

/-- The polyhedron of a finite simplicial complex on a finite type is compact. -/
theorem isCompact_stdSpace {ν : Type*} [Fintype ν] [DecidableEq ν] (Δ : Set (Finset ν)) :
    IsCompact (stdSpace Δ) :=
  (Set.toFinite Δ).isCompact_biUnion fun _ _ ↦ (Finset.finite_toSet _).isCompact_convexHull ℝ

/-- If the image of every open simplex of a standard triangulation of `S` lies in or misses
`{x}`, with `x ∈ S`, then `x` is the image of a vertex. -/
theorem IsStdTriangulation.exists_single_eq {ν σ : Type*} [Fintype ν] [DecidableEq ν]
    {Δ : Set (Finset ν)} {h : (ν → ℝ) → σ → ℝ} {S : Set (σ → ℝ)}
    (hT : IsStdTriangulation Δ h S) {x : σ → ℝ} (hx : x ∈ S)
    (hA : ∀ s ∈ Δ, h '' openStd s ⊆ {x} ∨ Disjoint (h '' openStd s) {x}) :
    ∃ w, Pi.single w (1 : ℝ) ∈ stdSpace Δ ∧ h (Pi.single w 1) = x := by
  obtain ⟨y₀, hy₀, rfl⟩ : x ∈ h '' stdSpace Δ := hT.image_eq ▸ hx
  obtain ⟨c, hc, hy₀c⟩ := hT.exists_mem_openStd hy₀
  obtain ⟨w, hw⟩ := hT.nonempty c hc
  have hcx : h '' openStd c ⊆ {h y₀} := (hA c hc).resolve_right fun h1 ↦
    absurd rfl (Set.disjoint_left.1 h1 ⟨y₀, hy₀c, rfl⟩)
  have hoc : openStd c ⊆ {y₀} := fun z hz ↦ hT.injOn
    (closedStd_subset_stdSpace hc (openStd_subset_closedStd c hz)) hy₀ (hcx ⟨z, hz, rfl⟩)
  have hw₀ := closure_mono hoc
    (closedStd_subset_closure_openStd ⟨w, hw⟩ (single_mem_closedStd hw))
  rw [closure_singleton, mem_singleton_iff] at hw₀
  subst hw₀
  exact ⟨w, hy₀, rfl⟩

/-- The open star `{y ∈ |Δ| | 0 < y w}` of a vertex `w` is star-convex about the vertex. -/
theorem IsStdTriangulation.starConvex_openStar {ν σ : Type*} [Fintype ν] [DecidableEq ν]
    {Δ : Set (Finset ν)} {h : (ν → ℝ) → σ → ℝ} {S : Set (σ → ℝ)}
    (hT : IsStdTriangulation Δ h S) (w : ν) :
    StarConvex ℝ (Pi.single w 1) (stdSpace Δ ∩ {y | 0 < y w}) := by
  intro y hy a b ha hb hab
  obtain ⟨t, ht, hyt⟩ := hT.exists_mem_openStd hy.1
  have hwt : w ∈ t := not_not.1 fun h' ↦ hy.2.ne' (hyt.2.2 w h')
  have hconv : Convex ℝ (closedStd t) := by
    rw [closedStd_eq_convexHull]
    exact convex_convexHull ℝ _
  refine ⟨closedStd_subset_stdSpace ht
    (hconv (single_mem_closedStd hwt) (openStd_subset_closedStd t hyt) ha hb hab), ?_⟩
  simp only [mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    simpa using hy.2
  · exact add_pos_of_pos_of_nonneg ha' (mul_nonneg hb (hyt.1 w hwt).le)

/-- If the image of every open simplex of a standard triangulation of `S` lies in or misses `A`,
and `A` contains the trace on `S` of an open neighbourhood of the image of a vertex `w`, then `A`
contains the image of the open star of `w`. -/
theorem IsStdTriangulation.image_openStar_subset {ν σ : Type*} [Fintype ν] [DecidableEq ν]
    {Δ : Set (Finset ν)} {h : (ν → ℝ) → σ → ℝ} {S : Set (σ → ℝ)}
    (hT : IsStdTriangulation Δ h S) {A W : Set (σ → ℝ)}
    (hA : ∀ t ∈ Δ, h '' openStd t ⊆ A ∨ Disjoint (h '' openStd t) A) (hW : IsOpen W)
    (hSW : S ∩ W ⊆ A) {w : ν} (hw : h (Pi.single w 1) ∈ W) :
    h '' (stdSpace Δ ∩ {y | 0 < y w}) ⊆ A := by
  rintro _ ⟨y, ⟨hy, hyw⟩, rfl⟩
  obtain ⟨t, ht, hyt⟩ := hT.exists_mem_openStd hy
  have hwt : w ∈ t := not_not.1 fun h' ↦ hyw.ne' (hyt.2.2 w h')
  refine (hA t ht).elim (fun h1 ↦ h1 ⟨y, hyt, rfl⟩) fun h1 ↦ ?_
  have hxcl : h (Pi.single w 1) ∈ closure (h '' openStd t) :=
    ((hT.continuousOn.mono (closedStd_subset_stdSpace ht)).mono (closure_minimal
      (openStd_subset_closedStd t) (isCompact_closedStd t).isClosed)).image_closure
      ⟨_, closedStd_subset_closure_openStd ⟨w, hwt⟩ (single_mem_closedStd hwt), rfl⟩
  obtain ⟨_, hzW, y', hy', rfl⟩ := mem_closure_iff.1 hxcl W hW hw
  have hy'S : h y' ∈ S := hT.image_eq ▸ mem_image_of_mem h
    (closedStd_subset_stdSpace ht (openStd_subset_closedStd t hy'))
  exact absurd (hSW ⟨hy'S, hzW⟩) (Set.disjoint_left.1 h1 ⟨y', hy', rfl⟩)

/-- The image of the open star of `w` is the complement in `S` of the image of the closed set
`{y ∈ |Δ| | y w ≤ 0}`. -/
theorem IsStdTriangulation.image_openStar_eq {ν σ : Type*} [DecidableEq ν]
    {Δ : Set (Finset ν)} {h : (ν → ℝ) → σ → ℝ} {S : Set (σ → ℝ)}
    (hT : IsStdTriangulation Δ h S) (w : ν) :
    h '' (stdSpace Δ ∩ {y | 0 < y w}) = S \ h '' (stdSpace Δ ∩ {y | y w ≤ 0}) := by
  rw [← hT.image_eq]
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hyw⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro ⟨y', ⟨hy', hy'w⟩, hyy⟩
    rw [hT.injOn hy' hy hyy] at hy'w
    simp only [mem_setOf_eq] at hy'w hyw
    linarith
  · rintro ⟨⟨y, hy, rfl⟩, hyK⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    by_contra h'
    exact hyK ⟨y, ⟨hy, show y w ≤ 0 from not_lt.1 h'⟩, rfl⟩

/-- If `V ∩ G ⊆ S` for an open `G`, and the image of the open star of a vertex `w` of a standard
triangulation of `S` lies in `V ∩ G`, then this image is the trace on `V` of an open set
containing the image of `w`. -/
theorem IsStdTriangulation.exists_isOpen_inter_eq_image_openStar {ν σ : Type*} [Fintype ν]
    [DecidableEq ν] {Δ : Set (Finset ν)} {h : (ν → ℝ) → σ → ℝ} {S : Set (σ → ℝ)}
    (hT : IsStdTriangulation Δ h S) {V G : Set (σ → ℝ)} (hG : IsOpen G) (hVG : V ∩ G ⊆ S)
    {w : ν} (hOG : h '' (stdSpace Δ ∩ {y | 0 < y w}) ⊆ V ∩ G)
    (hw : Pi.single w (1 : ℝ) ∈ stdSpace Δ) :
    ∃ W, IsOpen W ∧ h (Pi.single w 1) ∈ W ∧ W ∩ V = h '' (stdSpace Δ ∩ {y | 0 < y w}) := by
  have hK : IsClosed (h '' (stdSpace Δ ∩ {y | y w ≤ 0})) :=
    (((isCompact_stdSpace Δ).inter_right (isClosed_le (continuous_apply w)
      continuous_const)).image_of_continuousOn (hT.continuousOn.mono inter_subset_left)).isClosed
  refine ⟨(h '' (stdSpace Δ ∩ {y | y w ≤ 0}))ᶜ ∩ G, hK.isOpen_compl.inter hG,
    ⟨?_, (hOG ⟨_, ⟨hw, by simp⟩, rfl⟩).2⟩, ?_⟩
  · rintro ⟨y, ⟨hy, hyw⟩, hyx⟩
    rw [hT.injOn hy hw hyx] at hyw
    simp only [mem_setOf_eq, Pi.single_eq_same] at hyw
    norm_num at hyw
  · refine Subset.antisymm (fun z hz ↦ ?_) fun z hz ↦ ⟨⟨?_, (hOG hz).2⟩, (hOG hz).1⟩
    · rw [hT.image_openStar_eq w]
      exact ⟨hVG ⟨hz.2, hz.1.2⟩, hz.1.1⟩
    · rw [hT.image_openStar_eq w] at hz
      exact hz.2

/-- The image under a standard triangulation of a contractible subset of the polyhedron is
contractible. -/
theorem IsStdTriangulation.contractibleSpace_image {ν σ : Type*} [Fintype ν] [DecidableEq ν]
    {Δ : Set (Finset ν)} {h : (ν → ℝ) → σ → ℝ} {S : Set (σ → ℝ)}
    (hT : IsStdTriangulation Δ h S) {O : Set (ν → ℝ)} (hO : O ⊆ stdSpace Δ)
    [ContractibleSpace O] : ContractibleSpace (h '' O) := by
  haveI : CompactSpace (stdSpace Δ) := isCompact_iff_compactSpace.1 (isCompact_stdSpace Δ)
  have hemb : Topology.IsEmbedding (O.restrict h) :=
    (hT.continuousOn.restrict.isClosedEmbedding
      (fun a b hab ↦ Subtype.ext (hT.injOn a.2 b.2 hab))).isEmbedding.comp
      (Topology.IsEmbedding.inclusion hO)
  exact ((Homeomorph.setCongr (image_eq_range h O)).trans hemb.toHomeomorph.symm).contractibleSpace

/-- **Closed semialgebraic sets have small open contractible neighbourhoods.** If `V ⊆ ℝ^σ` is
closed and semialgebraic, `x ∈ V` and `U` is a neighbourhood of `x`, there is an open `W ∋ x`
with `W ∩ V ⊆ U` and `W ∩ V` contractible. -/
theorem exists_isOpen_contractibleSpace_inter {σ : Type} [Fintype σ] {V : Set (σ → ℝ)}
    (hV : IsSemialgebraic V) (hVc : IsClosed V) {x : σ → ℝ} (hx : x ∈ V) {U : Set (σ → ℝ)}
    (hU : U ∈ 𝓝 x) :
    ∃ W : Set (σ → ℝ), IsOpen W ∧ x ∈ W ∧ W ∩ V ⊆ U ∧ ContractibleSpace (W ∩ V : Set _) := by
  classical
  set q : (σ → ℝ) → ℝ := fun y ↦ ∑ i, (y i - x i) ^ 2
  have hqc : Continuous q := continuous_finset_sum _ fun i _ ↦
    ((continuous_apply i).sub continuous_const).pow 2
  have hqx : q x = 0 := by simp [q]
  have hball : ∀ ρ : ℝ, 0 ≤ ρ → {y | q y ≤ ρ ^ 2} ⊆ Metric.closedBall x ρ := fun _ hρ _ hy ↦
    Metric.mem_closedBall.2 (dist_le_of_sum_sq_sub_le hρ hy)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  set ρ := min (ε / 2) (1 / 2)
  have hρ : 0 < ρ := lt_min (half_pos hε) one_half_pos
  have hρε : ρ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hρ1 : ρ ^ 2 < 1 := by
    have : ρ ≤ 1 / 2 := min_le_right _ _
    nlinarith
  set S := V ∩ {y | q y ≤ 1}
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded (hVc.inter (isClosed_le hqc continuous_const))
      (Metric.isBounded_closedBall (x := x) (r := 1) |>.subset ?_)
    refine inter_subset_right.trans ?_
    simpa using hball 1 zero_le_one
  have hSs : IsSemialgebraic S := hV.inter (isSemialgebraic_sqDist_le x 1)
  set Wb := {y | q y < ρ ^ 2}
  have hWbo : IsOpen Wb := isOpen_lt hqc continuous_const
  have hxWb : x ∈ Wb := by
    simp only [Wb, mem_setOf_eq, hqx]
    positivity
  set A₂ := V ∩ Wb
  let A : Bool → Set (σ → ℝ) := fun b ↦ if b then {x} else A₂
  have hxS : x ∈ S := ⟨hx, by simp [hqx]⟩
  have hAs : ∀ b, IsSemialgebraic (A b) := Bool.forall_bool.2 ⟨hV.inter
    (isSemialgebraic_sqDist_lt x _), isSemialgebraic_singleton x⟩
  have hAS : ∀ b, A b ⊆ S := Bool.forall_bool.2
    ⟨fun y hy ↦ ⟨hy.1, hy.2.le.trans hρ1.le⟩, by simpa [A] using hxS⟩
  obtain ⟨ν, _, _, Δ, h, hT, hcompat⟩ := stdTriangulable σ S Bool A hSc hSs hAs hAS
  have hcompat' : ∀ b, ∀ s ∈ Δ, h '' openStd s ⊆ A b ∨ Disjoint (h '' openStd s) (A b) :=
    fun b s hs ↦ by rw [openStd_eq_openSimplex]; exact hcompat b s hs
  obtain ⟨w, hy₀, hy₀x⟩ := hT.exists_single_eq hxS (hcompat' true)
  have hOA : h '' (stdSpace Δ ∩ {y | 0 < y w}) ⊆ A₂ := hT.image_openStar_subset
    (hcompat' false) hWbo (fun z hz ↦ ⟨hz.1.1, hz.2⟩) (by rwa [hy₀x])
  obtain ⟨Wo, hWo, hxWo, hWoV⟩ := hT.exists_isOpen_inter_eq_image_openStar (V := V)
    (G := {y | q y < 1}) (isOpen_lt hqc continuous_const)
    (fun z hz ↦ ⟨hz.1, (show q z < 1 from hz.2).le⟩)
    (fun z hz ↦ ⟨(hOA hz).1, (hOA hz).2.trans hρ1⟩) hy₀
  refine ⟨Wo, hWo, hy₀x ▸ hxWo, ?_, ?_⟩
  · rw [hWoV]
    exact fun z hz ↦ hεU ((Metric.closedBall_subset_ball hρε)
      (hball ρ hρ.le (show q z ≤ ρ ^ 2 from le_of_lt (hOA hz).2)))
  · rw [hWoV]
    haveI := (hT.starConvex_openStar w).contractibleSpace ⟨_, hy₀, by simp⟩
    exact hT.contractibleSpace_image inter_subset_left

end OpenStar

end MMP
