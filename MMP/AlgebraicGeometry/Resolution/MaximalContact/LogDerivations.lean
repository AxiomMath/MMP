module

public import MMP.AlgebraicGeometry.Morphisms.Smooth.CoordinateDerivations
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# The chain rule and a basis of the logarithmic derivations (Kollár §3.d)

Let `k` be a field.

* **Chain rule.** Let `φ : Y → X` be a morphism of `k`-schemes, `x_1, …, x_n` local coordinates
  on an open `U ⊆ X` and `y_1, …, y_N` local coordinates on an open `V ⊆ Y`
  (`MMP.Resolution.IsLocalCoordinatesOn`). For every local section `h` of `𝒪_U`,
  `∂(φ^*h)/∂y_j = ∑_i φ^*(∂h/∂x_i) · ∂(φ^*x_i)/∂y_j`.
* **Logarithmic derivations** (Kollár 3.87). Let `X` be smooth over `k`, `S ⊆ X` a hypersurface
  and `x_1, …, x_n` local coordinates on an open `U` with `S ∩ U = (x_1 = 0)`. Then
  `Der_X(-log S)|_U` is the free `𝒪_U`-module on `x_1 ∂_1, ∂_2, …, ∂_n`.
* **Decomposition of the derivatives** (Kollár (3.87.2)). In the same setting, for an ideal
  sheaf `I` and `0 ≤ j ≤ s`, `D^{s-j}(-log S)(D^j(I)) = ∑_{i=0}^j D^{s-i}(-log S)(∂^i_{x_1} I)`
  on `U`.

## Main statements

* `MMP.Resolution.Kollar.partialDerivative_appLE_eq_sum`: the chain rule.
* `MMP.Resolution.Kollar.exists_basis_logDerivations`: `x_1 ∂_1, ∂_2, …, ∂_n` is a basis of
  `Der_X(-log S)` over every affine open of `U`.
* `MMP.Resolution.Kollar.higherLogDerivativeIdeal_higherDerivativeIdeal_eq_iSup`,
  `MMP.Resolution.Kollar.higherDerivativeIdeal_eq_iSup_higherLogDerivativeIdeal` (Kollár
  (3.87.2)): `D^{s-j}(-log S)(D^j(I)) = ∑_{i ≤ j} D^{s-i}(-log S)(∂^i_{x_1} I)`, and
  `D^s(I) = ∑_{i ≤ s} D^{s-i}(-log S)(∂^i_{x_1} I)`.

## Implementation notes

As in `MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative`, partial derivatives
and logarithmic derivations are read on the affine opens. In the chain rule `h` is a section
over an affine open `W' ⊆ U` and the identity is stated on every affine open
`W ⊆ V ∩ φ⁻¹(W')`; these cover `V ∩ φ⁻¹(U')` for every open `U' ⊆ U` and every
`h ∈ 𝒪_X(U')` (restricted to the affine opens `W' ⊆ U'`),
and sections of `𝒪_Y` agree when they agree on such a cover, so this is the identity of
functions on `V ∩ φ⁻¹(U')`. Smoothness of `X` and `Y` is not used in the chain rule, only the
coordinates, and is dropped.

In the second statement the condition `S ∩ U = (x_1 = 0)` is read as `𝒪_X(-S)(W) = (x_1|_W)`
for every affine open `W ⊆ U`, and the coordinates are indexed by `Fin (n + 1)`, `x_1` being
the coordinate of index `0`. Smoothness of `S` is implied on `U` by this condition and is not
used; smoothness of `X` is, to see that `x_1` is a non-zero-divisor (the local rings of `X` are
domains, and `x_1` vanishes on no open set since `dx_1 ≠ 0`).

The decomposition (3.87.2) is an identity of ideal sheaves on `U`, and the ideals `∂^i_{x_1} J`
(`MMP.Resolution.partialDerivativeIdeal`) are defined for coordinates on the whole scheme. It is
therefore stated for `U = X`, i.e. for the open subscheme `U` with its coordinates; sums of
ideal sheaves are suprema.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.73, 3.87, (3.87.2)]
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Resolution.Kollar

open MMP.Resolution MMP.Resolution.Bridges

/-! ### The chain rule -/

section ChainRule

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)}

private theorem appLE_algebraMap (φ : Y ⟶ X) (hφ : φ ≫ sX = sY) {W' : X.Opens} {W : Y.Opens}
    (hle : W ≤ φ ⁻¹ᵁ W') (c : k) :
    (φ.appLE W' W hle).hom (letI := MMP.Mori.sectionAlgebra sX W'; algebraMap k Γ(X, W') c) =
      (letI := MMP.Mori.sectionAlgebra sY W; algebraMap k Γ(Y, W) c) := by
  subst hφ
  have h := Scheme.Hom.appLE_comp_appLE φ sX ⊤ W' W (by simp) hle
  exact congrArg (fun t => ((Scheme.ΓSpecIso (.of k)).inv ≫ t).hom c) h

/-- **The chain rule** (Kollár §3.d). Let `φ : Y → X` be a morphism of `k`-schemes,
`x_1, …, x_n` local coordinates on an open `U ⊆ X` and `y_1, …, y_N` local coordinates on an
open `V ⊆ Y`. For affine opens `W' ⊆ U` and `W ⊆ V ∩ φ⁻¹(W')` and every `h ∈ 𝒪_X(W')`,
`∂(φ^*h)/∂y_j = ∑_i φ^*(∂h/∂x_i) · ∂(φ^*x_i)/∂y_j` on `W`. -/
@[mmp "lem_kr3d_chain_rule"]
theorem partialDerivative_appLE_eq_sum (φ : Y ⟶ X) (hφ : φ ≫ sX = sY) {U : X.Opens} {n : ℕ}
    {x : Fin n → Γ(X, U)} (hx : IsLocalCoordinatesOn sX U x) {V : Y.Opens} {N : ℕ}
    {y : Fin N → Γ(Y, V)} (hy : IsLocalCoordinatesOn sY V y) (W' : X.affineOpens)
    (hW' : W'.1 ≤ U) (W : Y.affineOpens) (hWV : W.1 ≤ V) (hWW' : W.1 ≤ φ ⁻¹ᵁ W'.1)
    (h : Γ(X, W')) (j : Fin N) :
    partialDerivative hy W hWV j ((φ.appLE W' W hWW').hom h) =
      ∑ i, (φ.appLE W' W hWW').hom (partialDerivative hx W' hW' i h) *
        partialDerivative hy W hWV j
          ((φ.appLE U W (hWW'.trans (φ.preimage_mono hW'))).hom (x i)) := by
  let := MMP.Mori.sectionAlgebra sX W'.1
  let := MMP.Mori.sectionAlgebra sY W.1
  let pb : Γ(X, W') →+* Γ(Y, W) := (φ.appLE W' W hWW').hom
  let : Algebra Γ(X, W') Γ(Y, W) := pb.toAlgebra
  have : IsScalarTower k Γ(X, W') Γ(Y, W) := IsScalarTower.of_algebraMap_eq fun c =>
    (appLE_algebraMap φ hφ hWW' c).symm
  let δ : Derivation k Γ(X, W') Γ(Y, W) :=
    (partialDerivation hy W hWV j).compAlgebraMap Γ(X, W')
  have hδ : ∀ g, δ g = partialDerivative hy W hWV j (pb g) := fun _ => rfl
  have key := derivation_eq_sum_partialDerivative_smul hx W' hW' Γ(Y, W) δ h
  rw [hδ] at key
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hδ, Algebra.smul_def]
  congr 2
  change (φ.appLE W' W hWW').hom ((X.presheaf.map (homOfLE hW').op).hom (x i)) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end ChainRule

/-! ### A basis of the logarithmic derivations -/

section LogBasis

variable {k : Type u} [Field k]

/-- The algebraic content of Kollár 3.87: if `da_0, …, da_n` is a basis of `Ω_{A/k}` and
`a_0` is a non-zero-divisor, the derivations `δ` with `δ(a_0) ∈ (a_0)` form a free module on
`a_0 ∂_0, ∂_1, …, ∂_n`. -/
private theorem exists_basis_of_mem_iff {A : Type*} [CommRing A] [Algebra k A] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) A (KaehlerDifferential k A)) (a : Fin (n + 1) → A)
    (hb : ∀ i, b i = KaehlerDifferential.D k A (a i)) (ha : ∀ c : A, c * a 0 = 0 → c = 0)
    (L : Submodule A (Derivation k A A))
    (hL : ∀ δ : Derivation k A A, δ ∈ L ↔ δ (a 0) ∈ Ideal.span {a 0}) :
    ∃ e : Module.Basis (Fin (n + 1)) A L, ∀ i, (e i : Derivation k A A) =
      if i = 0 then a 0 • (b.coord i).compDer (KaehlerDifferential.D k A)
      else (b.coord i).compDer (KaehlerDifferential.D k A) := by
  set p : Fin (n + 1) → Derivation k A A :=
    fun i => (b.coord i).compDer (KaehlerDifferential.D k A) with hp
  have hpa : ∀ i j, p i (a j) = if j = i then 1 else 0 := by
    intro i j
    change b.coord i (KaehlerDifferential.D k A (a j)) = _
    rw [← hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hsum : ∀ (f : Fin (n + 1) → Derivation k A A) (g : A), (∑ i, f i) g = ∑ i, f i g := by
    intro f g
    change (Derivation.coeFnAddMonoidHom (∑ i, f i)) g = _
    rw [map_sum, Finset.sum_apply]
    rfl
  have hexp : ∀ (δ : Derivation k A A) (g : A), δ g = ∑ i, δ (a i) * p i g := by
    intro δ g
    rw [← δ.liftKaehlerDifferential_comp_D g, ← b.sum_repr (KaehlerDifferential.D k A g),
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hb, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, mul_comm]
    rfl
  set v : Fin (n + 1) → Derivation k A A := fun i => if i = 0 then a 0 • p i else p i with hv
  have hvmem : ∀ i, v i ∈ L := by
    intro i
    rw [hL]
    by_cases hi : i = 0
    · subst hi
      simp only [hv, ite_true, Derivation.smul_apply, hpa, smul_eq_mul, mul_one]
      exact Ideal.mem_span_singleton_self _
    · simp only [hv, hi, ite_false, hpa, Ne.symm hi]
      exact zero_mem _
  let v' : Fin (n + 1) → L := fun i => ⟨v i, hvmem i⟩
  have hli : LinearIndependent A v' := by
    refine LinearIndependent.of_comp L.subtype ?_
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h := congrArg (fun δ : Derivation k A A => δ (a j)) hg
    simp only [Function.comp_apply, Submodule.subtype_apply, Derivation.zero_apply] at h
    rw [hsum] at h
    have hs : ∑ i, (g i • (v' i : Derivation k A A)) (a j) =
        (g j • (v' j : Derivation k A A)) (a j) := by
      refine Finset.sum_eq_single j (fun i _ hij => ?_) (by simp)
      simp only [v', hv, Derivation.smul_apply, smul_eq_mul]
      split_ifs <;> simp [hpa, Ne.symm hij]
    rw [hs] at h
    simp only [v', hv, Derivation.smul_apply, smul_eq_mul] at h
    by_cases hj : j = 0
    · subst hj
      simp only [ite_true, Derivation.smul_apply, smul_eq_mul, hpa, mul_one] at h
      exact ha _ h
    · simpa [hj, hpa] using h
  have hsp : ⊤ ≤ Submodule.span A (Set.range v') := by
    rintro ⟨δ, hδ⟩ -
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((hL δ).mp hδ)
    refine (Submodule.mem_span_range_iff_exists_fun A).mpr
      ⟨fun i => if i = 0 then c else δ (a i), ?_⟩
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    ext g
    rw [hexp δ g, hsum]
    simp only [Derivation.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = 0
    · subst hi
      simp only [v', hv, ite_true, Derivation.smul_apply, smul_eq_mul, ← hc]
      ring
    · simp [v', hv, hi]
  exact ⟨Module.Basis.mk hli hsp, fun i => by simp [v', hv, hp]⟩

variable {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {U : X.Opens} {n : ℕ} {x : Fin n → Γ(X, U)}

private theorem map_restrictSection (W W' : X.affineOpens) (hW : W.1 ≤ U) (h : W'.1 ≤ W.1)
    (g : Γ(X, U)) :
    (X.presheaf.map (homOfLE h).op).hom (restrictSection W hW g) =
      restrictSection W' (h.trans hW) g := by
  unfold restrictSection
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- On a smooth `k`-scheme a local coordinate is a non-zero-divisor on every affine open. -/
private theorem eq_zero_of_mul_restrictSection_eq_zero [Smooth sX]
    (hx : IsLocalCoordinatesOn sX U x) (W : X.affineOpens) (h : W.1 ≤ U) (i : Fin n)
    {c : Γ(X, W)} (hc : c * restrictSection W h (x i) = 0) : c = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf W.1 c 0 fun p hp => ?_
  have := isRegularLocalRing_stalk_of_smooth_over_field sX p
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk p)
  have hmul := congrArg (X.presheaf.germ W.1 p hp).hom hc
  rw [map_mul, map_zero] at hmul
  rcases mul_eq_zero.mp hmul with h0 | h0
  · rw [map_zero]
    exact h0
  · exfalso
    obtain ⟨V, hpV, hVaff, hVW, _, hV⟩ := X.presheaf.germ_eq_of_isBasis X.isBasis_affineOpens
      p hp hp (s := restrictSection W h (x i)) (t := 0) (by rw [map_zero]; exact h0)
    let V' : X.affineOpens := ⟨V, hVaff⟩
    have hres : restrictSection V' (hVW.trans h) (x i) = 0 := by
      rw [← map_restrictSection W V' h hVW (x i)]
      simpa using hV
    let := MMP.Mori.sectionAlgebra sX V
    have : Nontrivial Γ(X, V) := (X.presheaf.germ V p hpV).hom.domain_nontrivial
    refine (hx.basis V' (hVW.trans h)).ne_zero i ?_
    change (hx V' (hVW.trans h)).choose i = 0
    rw [(hx V' (hVW.trans h)).choose_spec i, hres, map_zero]

/-- **The logarithmic derivations along a hypersurface** (Kollár 3.87). Let `X` be smooth over
`k`, `S ⊆ X` a hypersurface and `x_1, …, x_n` local coordinates on an open `U` with
`S ∩ U = (x_1 = 0)`, i.e. `𝒪_X(-S)(W) = (x_1|_W)` for every affine open `W ⊆ U` (`x_1` being
the coordinate of index `0`). Then on every affine open `W ⊆ U`, `Der_X(-log S)(W)` is the free
`𝒪_X(W)`-module on `x_1 ∂_1, ∂_2, …, ∂_n`. -/
@[mmp "lem_kr3d_log_derivations_local_basis"]
theorem exists_basis_logDerivations [Smooth sX] {x : Fin (n + 1) → Γ(X, U)}
    (hx : IsLocalCoordinatesOn sX U x) (S : X.IdealSheafData)
    (hS : ∀ (W : X.affineOpens) (h : W.1 ≤ U),
      S.ideal W = Ideal.span {restrictSection W h (x 0)})
    (W : X.affineOpens) (h : W.1 ≤ U) :
    letI := MMP.Mori.sectionAlgebra sX W.1
    ∃ e : Module.Basis (Fin (n + 1)) Γ(X, W) (logDerivations sX S W), ∀ i,
      (e i : Derivation k Γ(X, W) Γ(X, W)) =
        if i = 0 then restrictSection W h (x 0) • partialDerivation hx W h 0
        else partialDerivation hx W h i := by
  let := MMP.Mori.sectionAlgebra sX W.1
  set t := restrictSection W h (x 0)
  have hL : ∀ δ : Derivation k Γ(X, W) Γ(X, W),
      δ ∈ logDerivations sX S W ↔ δ t ∈ Ideal.span {t} := by
    intro δ
    change (∀ f ∈ S.ideal W, δ f ∈ S.ideal W) ↔ _
    rw [hS W h]
    refine ⟨fun hδ => hδ t (Ideal.mem_span_singleton_self t), fun hδ f hf => ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hδ)
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t))
  obtain ⟨e, he⟩ := exists_basis_of_mem_iff (hx.basis W h) (fun i => restrictSection W h (x i))
    (hx W h).choose_spec (fun c hc => eq_zero_of_mul_restrictSection_eq_zero hx W h 0 hc)
    (logDerivations sX S W) hL
  refine ⟨e, fun i => ?_⟩
  rw [he i]
  by_cases hi : i = 0
  · subst hi
    rfl
  · simp only [hi, ite_false]
    rfl

end LogBasis

/-! ### Decomposition of the derivatives along a hypersurface -/

section LogDecomposition

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-! #### The lattice-theoretic part -/

private theorem iterate_biSup_comm {α : Type*} [CompleteLattice α] (f : α → α)
    (hf : ∀ (s : Finset ℕ) (K : ℕ → α), f (⨆ i ∈ s, K i) = ⨆ i ∈ s, f (K i)) (r : ℕ)
    (s : Finset ℕ) (K : ℕ → α) : f^[r] (⨆ i ∈ s, K i) = ⨆ i ∈ s, f^[r] (K i) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, hf]
    simp only [Function.iterate_succ_apply']

private theorem partial_iterate_le {α : Type*} [CompleteLattice α] (DL P : α → α)
    (hDL : Monotone DL)
    (hDLs : ∀ (s : Finset ℕ) (K : ℕ → α), DL (⨆ i ∈ s, K i) = ⨆ i ∈ s, DL (K i))
    (hd : ∀ K, P (DL K) ≤ DL (P K) ⊔ P K) (K : α) (m : ℕ) :
    P (DL^[m] K) ≤ ⨆ a ∈ Finset.range (m + 1), DL^[a] (P K) := by
  induction m with
  | zero => exact le_iSup₂_of_le 0 (by simp) le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    refine (hd _).trans (sup_le ?_ ?_)
    · refine (hDL ih).trans ?_
      rw [hDLs]
      refine iSup₂_le fun a ha => ?_
      exact le_iSup₂_of_le (a + 1) (by simp at ha ⊢; omega)
        (Function.iterate_succ_apply' DL a _).ge
    · exact ih.trans (iSup₂_le fun a ha =>
        le_iSup₂_of_le a (by simp at ha ⊢; omega) le_rfl)

private theorem iterate_derivative_eq_iSup {α : Type*} [CompleteLattice α] (D DL P : α → α)
    (hDL : Monotone DL) (hP : Monotone P)
    (hDLs : ∀ (s : Finset ℕ) (K : ℕ → α), DL (⨆ i ∈ s, K i) = ⨆ i ∈ s, DL (K i))
    (hPs : ∀ (s : Finset ℕ) (K : ℕ → α), P (⨆ i ∈ s, K i) = ⨆ i ∈ s, P (K i))
    (hD : ∀ K, D K = DL K ⊔ P K) (hb : ∀ K, K ≤ P K)
    (hd : ∀ K, P (DL K) ≤ DL (P K) ⊔ P K) (I : α) (j : ℕ) :
    D^[j] I = ⨆ i ∈ Finset.range (j + 1), DL^[j - i] (P^[i] I) := by
  induction j with
  | zero => simp
  | succ j ih =>
    set R : α := ⨆ i ∈ Finset.range (j + 1), DL^[j - i] (P^[i] I) with hR
    have hterm : ∀ a i, i + a ≤ j → DL^[a] (P^[i] I) ≤ R := by
      intro a i hia
      refine (Monotone.iterate hDL a
        (Function.monotone_iterate_of_id_le hb (show i ≤ j - a by omega) I)).trans ?_
      refine le_iSup₂_of_le (j - a) (by simp only [Finset.mem_range]; omega) ?_
      have : j - (j - a) = a := by omega
      rw [this]
    have hPj : P^[j] I ≤ R := by
      simpa using hterm 0 j (by omega)
    have hRB : R ≤ DL R ⊔ P^[j + 1] I := by
      refine iSup₂_le fun i hi => ?_
      have hi' : i ≤ j := by simp at hi; omega
      rcases Nat.eq_zero_or_pos (j - i) with h0 | hpos
      · have : i = j := by omega
        subst this
        simp only [Nat.sub_self, Function.iterate_zero, id]
        exact (Function.monotone_iterate_of_id_le hb (Nat.le_succ i) I).trans le_sup_right
      · obtain ⟨a, ha⟩ : ∃ a, j - i = a + 1 := ⟨j - i - 1, by omega⟩
        rw [ha, Function.iterate_succ_apply']
        exact (hDL (hterm a i (by omega))).trans le_sup_left
    have hPR : P R ≤ DL R ⊔ P^[j + 1] I := by
      rw [hR, hPs]
      refine iSup₂_le fun i hi => ?_
      have hi' : i ≤ j := by simp at hi; omega
      refine (partial_iterate_le DL P hDL hDLs hd (P^[i] I) (j - i)).trans ?_
      refine iSup₂_le fun a ha => ?_
      have ha' : a ≤ j - i := by simp at ha; omega
      rw [← Function.iterate_succ_apply' P i I]
      by_cases hlt : i.succ + a ≤ j
      · exact (hterm a i.succ hlt).trans hRB
      · rcases a with _ | a'
        · have : i = j := by omega
          subst this
          simp only [Function.iterate_zero, id]
          exact le_sup_right
        · rw [Function.iterate_succ_apply']
          exact (hDL (hterm a' i.succ (by omega))).trans le_sup_left
    have hRsucc : (⨆ i ∈ Finset.range (j + 1 + 1), DL^[j + 1 - i] (P^[i] I)) =
        DL R ⊔ P^[j + 1] I := by
      rw [Finset.range_add_one (n := j + 1), Finset.iSup_insert, hR, hDLs, sup_comm]
      congr 1
      · refine iSup_congr fun i => iSup_congr fun hi => ?_
        have hi' : i ≤ j := by simp at hi; omega
        have : j + 1 - i = (j - i) + 1 := by omega
        rw [this, Function.iterate_succ_apply']
      · simp
    rw [hRsucc, Function.iterate_succ_apply', ih, hD]
    refine le_antisymm (sup_le le_sup_left hPR) (sup_le_sup_left ?_ _)
    rw [Function.iterate_succ_apply']
    exact hP hPj

private theorem iterate_log_derivative_eq_iSup {α : Type*} [CompleteLattice α]
    (D DL P : α → α) (hDL : Monotone DL) (hP : Monotone P)
    (hDLs : ∀ (s : Finset ℕ) (K : ℕ → α), DL (⨆ i ∈ s, K i) = ⨆ i ∈ s, DL (K i))
    (hPs : ∀ (s : Finset ℕ) (K : ℕ → α), P (⨆ i ∈ s, K i) = ⨆ i ∈ s, P (K i))
    (hD : ∀ K, D K = DL K ⊔ P K) (hb : ∀ K, K ≤ P K)
    (hd : ∀ K, P (DL K) ≤ DL (P K) ⊔ P K) (I : α) {j s : ℕ} (hjs : j ≤ s) :
    DL^[s - j] (D^[j] I) = ⨆ i ∈ Finset.range (j + 1), DL^[s - i] (P^[i] I) := by
  rw [iterate_derivative_eq_iSup D DL P hDL hP hDLs hPs hD hb hd I j,
    iterate_biSup_comm DL hDLs]
  refine iSup_congr fun i => iSup_congr fun hi => ?_
  have hi' : i ≤ j := by simp at hi; omega
  rw [← Function.iterate_add_apply]
  have : s - j + (j - i) = s - i := by omega
  rw [this]

/-! #### Ideal sheaves generated by a family of Leibniz operators -/

/-- A family of additive Leibniz operators `Γ(X, W) → Γ(X, W)`, indexed by `ι`, one family for
each affine open `W`, compatible with the restriction maps. -/
structure OpFamily (X : Scheme.{u}) (ι : Type) where
  /-- The operator with index `l` on the sections over the affine open `W`. -/
  op : ∀ W : X.affineOpens, ι → Γ(X, W) → Γ(X, W)
  /-- Each operator is additive. -/
  op_add : ∀ W l a b, op W l (a + b) = op W l a + op W l b
  /-- Each operator satisfies the Leibniz rule. -/
  op_mul : ∀ W l a b, op W l (a * b) = a * op W l b + b * op W l a
  /-- The operators commute with restriction to a smaller affine open. -/
  op_res : ∀ (W W' : X.affineOpens) (h : W'.1 ≤ W.1) l a,
    (X.presheaf.map (homOfLE h).op).hom (op W l a) =
      op W' l ((X.presheaf.map (homOfLE h).op).hom a)

namespace OpFamily

variable {Y : Scheme.{u}} {ι : Type} (F : OpFamily Y ι)

private theorem op_zero (W : Y.affineOpens) (l : ι) : F.op W l 0 = 0 := by
  simpa using F.op_add W l 0 0

/-- The ideal of `Γ(Y, W)` generated by the `F_l(g)`, `g ∈ K(W)`. -/
private def ideal (K : Y.IdealSheafData) (W : Y.affineOpens) : Ideal Γ(Y, W) :=
  Ideal.span {y | ∃ l, ∃ g ∈ K.ideal W, y = F.op W l g}

private theorem op_mem {K : Y.IdealSheafData} {W : Y.affineOpens} {g : Γ(Y, W)} (hg : g ∈ K.ideal W)
    (l : ι) : F.op W l g ∈ F.ideal K W :=
  Ideal.subset_span ⟨l, g, hg, rfl⟩

private theorem ideal_le_iff {K : Y.IdealSheafData} {W : Y.affineOpens} {J : Ideal Γ(Y, W)} :
    F.ideal K W ≤ J ↔ ∀ l, ∀ g ∈ K.ideal W, F.op W l g ∈ J := by
  unfold ideal
  rw [Ideal.span_le]
  constructor
  · intro h l g hg
    exact h ⟨l, g, hg, rfl⟩
  · rintro h _ ⟨l, g, hg, rfl⟩
    exact h l g hg

private theorem map_ideal_basicOpen (K : Y.IdealSheafData) (W : Y.affineOpens) (f : Γ(Y, W)) :
    (F.ideal K W).map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom =
      F.ideal K (Y.affineBasicOpen f) := by
  have inst := W.2.isLocalization_basicOpen f
  have hρ : (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom =
      algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) := rfl
  apply le_antisymm
  · rw [ideal, Ideal.map_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨_, ⟨l, g, hg, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨l, _, ?_,
      F.op_res W (Y.affineBasicOpen f) (Y.basicOpen_le f) l g⟩
    rw [← K.map_ideal_basicOpen]
    exact Ideal.mem_map_of_mem _ hg
  · refine (F.ideal_le_iff).2 fun l (h : Γ(Y, Y.basicOpen f)) hh => ?_
    rw [← K.map_ideal_basicOpen] at hh
    obtain ⟨⟨g, s⟩, hgs⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f)
      Γ(Y, Y.basicOpen f)).mp hh
    have E4 : h * algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) s =
        algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) g := hgs
    let op' : Γ(Y, Y.basicOpen f) → Γ(Y, Y.basicOpen f) := F.op (Y.affineBasicOpen f) l
    have hmul : ∀ a b, op' (a * b) = a * op' b + b * op' a :=
      F.op_mul (Y.affineBasicOpen f) l
    have hres : ∀ a : Γ(Y, W), op' (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) a) =
        algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) (F.op W l a) := fun a =>
      (F.op_res W (Y.affineBasicOpen f) (Y.basicOpen_le f) l a).symm
    have E3 := congrArg op' E4
    rw [hmul, hres, hres] at E3
    change op' h ∈ _
    have key : algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) ((s : Γ(Y, W)) ^ 2) * op' h =
        algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f)
          ((s : Γ(Y, W)) * F.op W l g - g * F.op W l s) := by
      simp only [map_mul, map_pow, map_sub]
      linear_combination (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) s) * E3 -
        (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) (F.op W l s)) * E4
    have hmem : (s : Γ(Y, W)) * F.op W l g - g * F.op W l s ∈ F.ideal K W := by
      have h1 : F.op W l g ∈ F.ideal K W := F.op_mem g.2 l
      have h2 : F.op W l ((s : Γ(Y, W)) * g) ∈ F.ideal K W :=
        F.op_mem (Ideal.mul_mem_left _ _ g.2) l
      have e : (s : Γ(Y, W)) * F.op W l g - g * F.op W l s =
          (2 * (s : Γ(Y, W))) * F.op W l g - F.op W l ((s : Γ(Y, W)) * g) := by
        rw [F.op_mul]; ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) h2
    have hu : IsUnit (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) ((s : Γ(Y, W)) ^ 2)) :=
      IsLocalization.map_units Γ(Y, Y.basicOpen f)
        (⟨(s : Γ(Y, W)) ^ 2, Submonoid.pow_mem _ s.2 2⟩ : Submonoid.powers f)
    have hm : algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f)
        ((s : Γ(Y, W)) * F.op W l g - g * F.op W l s) ∈
        (F.ideal K W).map (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f)) :=
      Ideal.mem_map_of_mem _ hmem
    rw [← key] at hm
    have := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : Γ(Y, Y.basicOpen f)) hm
    rwa [← mul_assoc, hu.val_inv_mul, one_mul] at this

/-- The ideal sheaf generated by the `F_l(g)`, `g` a local section of `K`. -/
private def sheaf (K : Y.IdealSheafData) : Y.IdealSheafData where
  ideal := F.ideal K
  map_ideal_basicOpen := F.map_ideal_basicOpen K

private theorem sheaf_le_iff {K L : Y.IdealSheafData} :
    F.sheaf K ≤ L ↔ ∀ (W : Y.affineOpens) l, ∀ g ∈ K.ideal W, F.op W l g ∈ L.ideal W := by
  rw [Scheme.IdealSheafData.le_def]
  exact ⟨fun h W l g hg => h W (F.op_mem hg l),
    fun h W => (F.ideal_le_iff).2 (h W)⟩

private theorem sheaf_mono : Monotone F.sheaf := fun _ _ h =>
  F.sheaf_le_iff.2 fun W l _ hg => F.op_mem (h W hg) l

private theorem sheaf_sup (K K' : Y.IdealSheafData) :
    F.sheaf (K ⊔ K') = F.sheaf K ⊔ F.sheaf K' := by
  refine le_antisymm (F.sheaf_le_iff.2 fun W l g hg => ?_)
    (sup_le (F.sheaf_mono le_sup_left) (F.sheaf_mono le_sup_right))
  change g ∈ K.ideal W ⊔ K'.ideal W at hg
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hg
  rw [F.op_add]
  exact Submodule.add_mem_sup (F.op_mem ha l) (F.op_mem hb l)

private theorem sheaf_bot : F.sheaf ⊥ = ⊥ := by
  refine le_antisymm (F.sheaf_le_iff.2 fun W l g hg => ?_) bot_le
  have : g = 0 := hg
  rw [this, F.op_zero]
  exact zero_mem _

private theorem sheaf_biSup (s : Finset ℕ) (K : ℕ → Y.IdealSheafData) :
    F.sheaf (⨆ i ∈ s, K i) = ⨆ i ∈ s, F.sheaf (K i) := by
  induction s using Finset.induction_on with
  | empty => simp [sheaf_bot]
  | insert a s ha ih => rw [Finset.iSup_insert, Finset.iSup_insert, sheaf_sup, ih]

end OpFamily

/-! #### The operator families of the coordinates -/

section Concrete

variable {n : ℕ} {x : Fin (n + 1) → Γ(X, ⊤)}

private theorem partialDerivative_add' (hx : IsLocalCoordinatesOn sX ⊤ x) (W : X.affineOpens)
    (l : Fin (n + 1)) (a b : Γ(X, W)) :
    partialDerivative hx W le_top l (a + b) =
      partialDerivative hx W le_top l a + partialDerivative hx W le_top l b := by
  let := MMP.Mori.sectionAlgebra sX W.1
  simp only [← partialDerivation_apply]
  exact map_add _ a b

private theorem partialDerivative_mul' (hx : IsLocalCoordinatesOn sX ⊤ x) (W : X.affineOpens)
    (l : Fin (n + 1)) (a b : Γ(X, W)) :
    partialDerivative hx W le_top l (a * b) =
      a * partialDerivative hx W le_top l b + b * partialDerivative hx W le_top l a := by
  let := MMP.Mori.sectionAlgebra sX W.1
  simp only [← partialDerivation_apply]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

private theorem partialDerivative_coordinate' (hx : IsLocalCoordinatesOn sX ⊤ x)
    (W : X.affineOpens) (l : Fin (n + 1)) :
    partialDerivative hx W le_top l (restrictSection W le_top (x l)) = 1 := by
  rw [partialDerivative_restrictSection_coordinate]
  simp

private theorem partialDerivative_res (hx : IsLocalCoordinatesOn sX ⊤ x) (W W' : X.affineOpens)
    (h : W'.1 ≤ W.1) (l : Fin (n + 1)) (a : Γ(X, W)) :
    (X.presheaf.map (homOfLE h).op).hom (partialDerivative hx W le_top l a) =
      partialDerivative hx W' le_top l ((X.presheaf.map (homOfLE h).op).hom a) := by
  have hφ : (𝟙 X : X ⟶ X) ≫ sX = sX := Category.id_comp sX
  have hid : ∀ (V V' : X.Opens) (e : V' ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ V) (b : Γ(X, V)),
      (Scheme.Hom.appLE (𝟙 X : X ⟶ X) V V' e).hom b =
        (X.presheaf.map (homOfLE (show V' ≤ V from e)).op).hom b := by
    intro V V' e b
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    rfl
  have := partialDerivative_appLE_eq_sum (𝟙 X : X ⟶ X) hφ hx hx W le_top W' le_top h a l
  rw [hid W W' h a] at this
  rw [this]
  simp only [hid]
  have hc : ∀ i, partialDerivative hx W' le_top l
      ((X.presheaf.map (homOfLE (le_top : W'.1 ≤ ⊤)).op).hom (x i)) = if l = i then 1 else 0 :=
    fun i => partialDerivative_restrictSection_coordinate hx W' le_top l i
  simp only [hc]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact (hid _ _ h _).symm

private theorem partialDerivative_one' (hx : IsLocalCoordinatesOn sX ⊤ x) (W : X.affineOpens)
    (l : Fin (n + 1)) : partialDerivative hx W le_top l 1 = 0 := by
  let := MMP.Mori.sectionAlgebra sX W.1
  simp only [← partialDerivation_apply]
  exact Derivation.map_one_eq_zero _

private theorem partialDerivative_zero' (hx : IsLocalCoordinatesOn sX ⊤ x) (W : X.affineOpens)
    (l : Fin (n + 1)) : partialDerivative hx W le_top l 0 = 0 := by
  let := MMP.Mori.sectionAlgebra sX W.1
  simp only [← partialDerivation_apply]
  exact map_zero _

private theorem partialDerivative_comm (hx : IsLocalCoordinatesOn sX ⊤ x) (W : X.affineOpens)
    (l l' : Fin (n + 1)) (a : Γ(X, W)) :
    partialDerivative hx W le_top l (partialDerivative hx W le_top l' a) =
      partialDerivative hx W le_top l' (partialDerivative hx W le_top l a) := by
  let := MMP.Mori.sectionAlgebra sX W.1
  have key := derivation_eq_sum_partialDerivative_smul hx W le_top Γ(X, W)
    ⁅partialDerivation hx W le_top l, partialDerivation hx W le_top l'⁆ a
  have h0 : ∀ i, (⁅partialDerivation hx W le_top l, partialDerivation hx W le_top l'⁆ :
      Derivation k Γ(X, W) Γ(X, W)) (restrictSection W le_top (x i)) = 0 := by
    intro i
    rw [Derivation.commutator_apply]
    simp only [partialDerivation_apply, partialDerivative_restrictSection_coordinate]
    split_ifs <;> simp [partialDerivative_one', partialDerivative_zero']
  simp only [h0, smul_zero, Finset.sum_const_zero] at key
  rw [Derivation.commutator_apply] at key
  simp only [partialDerivation_apply] at key
  exact sub_eq_zero.mp key

/-- The partial derivatives `∂_l` as a family of operators. -/
private def partialFamily (hx : IsLocalCoordinatesOn sX ⊤ x) : OpFamily X (Fin (n + 1)) where
  op W l g := partialDerivative hx W le_top l g
  op_add W l a b := partialDerivative_add' hx W l a b
  op_mul W l a b := partialDerivative_mul' hx W l a b
  op_res W W' h l a := partialDerivative_res hx W W' h l a

/-- The family `x_1 ∂_1, ∂_2, …, ∂_n` generating `Der_X(-log S)`. -/
private def logFamily (hx : IsLocalCoordinatesOn sX ⊤ x) : OpFamily X (Fin (n + 1)) where
  op W l g := if l = 0 then restrictSection W le_top (x 0) * partialDerivative hx W le_top 0 g
    else partialDerivative hx W le_top l g
  op_add W l a b := by
    split_ifs
    · rw [partialDerivative_add']; ring
    · rw [partialDerivative_add']
  op_mul W l a b := by
    split_ifs
    · rw [partialDerivative_mul']; ring
    · rw [partialDerivative_mul']
  op_res W W' h l a := by
    split_ifs
    · rw [map_mul, partialDerivative_res, map_restrictSection W W' le_top h]
    · rw [partialDerivative_res]

/-- The family `∂_1, 0, …, 0`. -/
private def firstFamily (hx : IsLocalCoordinatesOn sX ⊤ x) : OpFamily X (Fin (n + 1)) where
  op W l g := if l = 0 then partialDerivative hx W le_top 0 g else 0
  op_add W l a b := by
    split_ifs
    · rw [partialDerivative_add']
    · simp
  op_mul W l a b := by
    split_ifs
    · rw [partialDerivative_mul']
    · simp
  op_res W W' h l a := by
    split_ifs
    · rw [partialDerivative_res]
    · simp

private theorem logFamily_op_zero (hx : IsLocalCoordinatesOn sX ⊤ x) (W : X.affineOpens)
    (g : Γ(X, W)) : (logFamily hx).op W 0 g =
      restrictSection W le_top (x 0) * partialDerivative hx W le_top 0 g := by
  simp [logFamily]

private theorem logFamily_op_ne (hx : IsLocalCoordinatesOn sX ⊤ x) (W : X.affineOpens)
    {l : Fin (n + 1)} (hl : l ≠ 0) (g : Γ(X, W)) :
    (logFamily hx).op W l g = partialDerivative hx W le_top l g := by
  simp [logFamily, hl]

private theorem firstFamily_op_zero (hx : IsLocalCoordinatesOn sX ⊤ x) (W : X.affineOpens)
    (g : Γ(X, W)) : (firstFamily hx).op W 0 g = partialDerivative hx W le_top 0 g := by
  simp [firstFamily]

private theorem firstFamily_op_ne (hx : IsLocalCoordinatesOn sX ⊤ x) (W : X.affineOpens)
    {l : Fin (n + 1)} (hl : l ≠ 0) (g : Γ(X, W)) : (firstFamily hx).op W l g = 0 := by
  simp [firstFamily, hl]

private theorem mem_sup_left' {A B : X.IdealSheafData} {W : X.affineOpens} {y : Γ(X, W)}
    (h : y ∈ A.ideal W) : y ∈ (A ⊔ B).ideal W :=
  (Submodule.mem_sup_left h : y ∈ A.ideal W ⊔ B.ideal W)

private theorem mem_sup_right' {A B : X.IdealSheafData} {W : X.affineOpens} {y : Γ(X, W)}
    (h : y ∈ B.ideal W) : y ∈ (A ⊔ B).ideal W :=
  (Submodule.mem_sup_right h : y ∈ A.ideal W ⊔ B.ideal W)

private theorem partialFamily_sheaf_eq (hx : IsLocalCoordinatesOn sX ⊤ x)
    (K : X.IdealSheafData) :
    (partialFamily hx).sheaf K = (logFamily hx).sheaf K ⊔ (firstFamily hx).sheaf K := by
  refine le_antisymm ((partialFamily hx).sheaf_le_iff.2 fun W l g hg => ?_)
    (sup_le ((logFamily hx).sheaf_le_iff.2 fun W l g hg => ?_)
      ((firstFamily hx).sheaf_le_iff.2 fun W l g hg => ?_))
  · by_cases hl : l = 0
    · subst hl
      have := (firstFamily hx).op_mem hg 0
      rw [firstFamily_op_zero] at this
      exact mem_sup_right' this
    · have := (logFamily hx).op_mem hg l
      rw [logFamily_op_ne hx W hl] at this
      exact mem_sup_left' this
  · by_cases hl : l = 0
    · subst hl
      rw [logFamily_op_zero]
      exact Ideal.mul_mem_left _ _ ((partialFamily hx).op_mem hg 0)
    · rw [logFamily_op_ne hx W hl]
      exact (partialFamily hx).op_mem hg l
  · by_cases hl : l = 0
    · subst hl
      rw [firstFamily_op_zero]
      exact (partialFamily hx).op_mem hg 0
    · rw [firstFamily_op_ne hx W hl]
      exact zero_mem _

private theorem le_firstFamily_sheaf (hx : IsLocalCoordinatesOn sX ⊤ x)
    (K : X.IdealSheafData) : K ≤ (firstFamily hx).sheaf K := by
  refine Scheme.IdealSheafData.le_def.2 fun W g hg => ?_
  have h1 := (firstFamily hx).op_mem (Ideal.mul_mem_left _ (restrictSection W le_top (x 0)) hg) 0
  have h2 := (firstFamily hx).op_mem hg 0
  rw [firstFamily_op_zero] at h1 h2
  have e : g = partialDerivative hx W le_top 0 (restrictSection W le_top (x 0) * g) -
      restrictSection W le_top (x 0) * partialDerivative hx W le_top 0 g := by
    rw [partialDerivative_mul', partialDerivative_coordinate']
    ring
  change g ∈ (firstFamily hx).ideal K W
  rw [e]
  exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ h2)

private theorem firstFamily_logFamily_le (hx : IsLocalCoordinatesOn sX ⊤ x)
    (K : X.IdealSheafData) :
    (firstFamily hx).sheaf ((logFamily hx).sheaf K) ≤
      (logFamily hx).sheaf ((firstFamily hx).sheaf K) ⊔ (firstFamily hx).sheaf K := by
  set M := (logFamily hx).sheaf ((firstFamily hx).sheaf K) ⊔ (firstFamily hx).sheaf K
  have hFK : ∀ (W : X.affineOpens) (g : Γ(X, W)), g ∈ K.ideal W →
      g ∈ ((firstFamily hx).sheaf K).ideal W := fun W g hg =>
    (Scheme.IdealSheafData.le_def.1 (le_firstFamily_sheaf hx K)) W hg
  have claim : ∀ (W : X.affineOpens) (y : Γ(X, W)), y ∈ (logFamily hx).ideal K W →
      y ∈ M.ideal W ∧ partialDerivative hx W le_top 0 y ∈ M.ideal W := by
    intro W y hy
    unfold OpFamily.ideal at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, g0, hg0, rfl⟩ := hy
      refine ⟨mem_sup_left' ((logFamily hx).op_mem (hFK W g0 hg0) l), ?_⟩
      have h0 := (firstFamily hx).op_mem hg0 0
      rw [firstFamily_op_zero] at h0
      replace h0 : partialDerivative hx W le_top 0 g0 ∈ ((firstFamily hx).sheaf K).ideal W := h0
      by_cases hl : l = 0
      · subst hl
        rw [logFamily_op_zero, partialDerivative_mul', partialDerivative_coordinate']
        refine Ideal.add_mem _ (mem_sup_left' ?_) ?_
        · have := (logFamily hx).op_mem h0 0
          rw [logFamily_op_zero] at this
          exact this
        · rw [mul_one]
          exact mem_sup_right' h0
      · rw [logFamily_op_ne hx W hl, partialDerivative_comm hx W 0 l]
        refine mem_sup_left' ?_
        have := (logFamily hx).op_mem h0 l
        rw [logFamily_op_ne hx W hl] at this
        exact this
    | zero =>
      refine ⟨zero_mem _, ?_⟩
      rw [partialDerivative_zero']
      exact zero_mem _
    | add a b _ _ ha hb =>
      refine ⟨add_mem ha.1 hb.1, ?_⟩
      rw [partialDerivative_add']
      exact add_mem ha.2 hb.2
    | smul a y _ hy =>
      refine ⟨Ideal.mul_mem_left _ _ hy.1, ?_⟩
      rw [smul_eq_mul, partialDerivative_mul']
      exact add_mem (Ideal.mul_mem_left _ _ hy.2) (Ideal.mul_mem_right _ _ hy.1)
  refine (firstFamily hx).sheaf_le_iff.2 fun W l y hy => ?_
  by_cases hl : l = 0
  · subst hl
    rw [firstFamily_op_zero]
    exact (claim W y hy).2
  · rw [firstFamily_op_ne hx W hl]
    exact zero_mem _

private theorem derivativeIdeal_eq_partialFamily [Smooth sX] (hx : IsLocalCoordinatesOn sX ⊤ x)
    (K : X.IdealSheafData) : derivativeIdeal sX K = (partialFamily hx).sheaf K := by
  refine Scheme.IdealSheafData.ext (funext fun W => ?_)
  rw [derivativeIdeal_ideal sX K W]
  let := MMP.Mori.sectionAlgebra sX W.1
  refine le_antisymm ?_ ((partialFamily hx).ideal_le_iff.2 fun l g hg => ?_)
  · unfold sectionDerivativeIdeal derivativeIdealOfRing
    refine Ideal.span_le.2 ?_
    rintro _ ⟨δ, f, hf, rfl⟩
    rw [derivation_eq_sum_partialDerivative_smul hx W le_top Γ(X, W) δ f]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ((partialFamily hx).op_mem hf i)
  · unfold sectionDerivativeIdeal derivativeIdealOfRing
    exact Ideal.subset_span ⟨partialDerivation hx W le_top l, g, hg, rfl⟩

private theorem firstStep_eq (hx : IsLocalCoordinatesOn sX ⊤ x) (K : X.IdealSheafData) :
    sInf {J'' : X.IdealSheafData | ∀ (W : X.affineOpens), ∀ f ∈ K.ideal W,
      partialDerivative hx W le_top 0 f ∈ J''.ideal W} = (firstFamily hx).sheaf K := by
  refine le_antisymm (sInf_le fun W f hf => ?_) (le_sInf fun J'' hJ'' => ?_)
  · have := (firstFamily hx).op_mem hf 0
    rw [firstFamily_op_zero] at this
    exact this
  · refine (firstFamily hx).sheaf_le_iff.2 fun W l g hg => ?_
    by_cases hl : l = 0
    · subst hl
      rw [firstFamily_op_zero]
      exact hJ'' W g hg
    · rw [firstFamily_op_ne hx W hl]
      exact zero_mem _

/-- The `k`-derivations in the basis of `Der_X(-log S)` act as the operators of `logFamily`. -/
private theorem logDerivations_basis_apply [Smooth sX] (hx : IsLocalCoordinatesOn sX ⊤ x)
    (S : X.IdealSheafData)
    (hS : ∀ W : X.affineOpens, S.ideal W = Ideal.span {restrictSection W le_top (x 0)})
    (W : X.affineOpens) :
    letI := MMP.Mori.sectionAlgebra sX W.1
    ∃ e : Module.Basis (Fin (n + 1)) Γ(X, W) (logDerivations sX S W),
      ∀ (i : Fin (n + 1)) (g : Γ(X, W)),
        (e i : Derivation k Γ(X, W) Γ(X, W)) g = (logFamily hx).op W i g := by
  let := MMP.Mori.sectionAlgebra sX W.1
  obtain ⟨e, he⟩ := exists_basis_logDerivations hx S (fun W _ => hS W) W le_top
  refine ⟨e, fun i g => ?_⟩
  rw [he i]
  by_cases hi : i = 0
  · subst hi
    rw [logFamily_op_zero]
    simp [partialDerivation_apply]
  · rw [logFamily_op_ne hx W hi]
    simp [hi, partialDerivation_apply]

private theorem logDerivativeIdeal_eq_logFamily [Smooth sX] (hx : IsLocalCoordinatesOn sX ⊤ x)
    (S : X.IdealSheafData)
    (hS : ∀ W : X.affineOpens, S.ideal W = Ideal.span {restrictSection W le_top (x 0)})
    (K : X.IdealSheafData) : logDerivativeIdeal sX S K = (logFamily hx).sheaf K := by
  refine le_antisymm (sInf_le fun W => ?_) (le_sInf fun L hL => ?_)
  · let := MMP.Mori.sectionAlgebra sX W.1
    obtain ⟨e, he⟩ := logDerivations_basis_apply hx S hS W
    unfold sectionLogDerivativeIdeal
    refine Ideal.span_le.2 ?_
    rintro _ ⟨δ, hδ, f, hf, rfl⟩
    have hmem : ∀ δ' : logDerivations sX S W,
        (δ' : Derivation k Γ(X, W) Γ(X, W)) f ∈ (logFamily hx).ideal K W := by
      intro δ'
      have hsp : δ' ∈ Submodule.span Γ(X, W) (Set.range e) := by
        rw [e.span_eq]; trivial
      induction hsp using Submodule.span_induction with
      | mem δ'' h =>
        obtain ⟨i, rfl⟩ := h
        rw [he]
        exact (logFamily hx).op_mem hf i
      | zero =>
        rw [Submodule.coe_zero, Derivation.zero_apply]
        exact zero_mem _
      | add a b _ _ ha hb =>
        rw [Submodule.coe_add, Derivation.add_apply]
        exact add_mem ha hb
      | smul c d _ hd =>
        rw [Submodule.coe_smul, Derivation.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_left _ c hd
    exact hmem ⟨δ, hδ⟩
  · refine (logFamily hx).sheaf_le_iff.2 fun W l g hg => ?_
    let := MMP.Mori.sectionAlgebra sX W.1
    obtain ⟨e, he⟩ := logDerivations_basis_apply hx S hS W
    rw [← he l g]
    exact hL W (Ideal.subset_span ⟨(e l : Derivation k Γ(X, W) Γ(X, W)), (e l).2, g, hg, rfl⟩)

end Concrete

/-- **Kollár (3.87.2).** Let `X` be smooth over `k`, `S ⊆ X` a hypersurface and
`x_1, …, x_n` local coordinates on `X` with `S = (x_1 = 0)`, i.e. `𝒪_X(-S)(W) = (x_1|_W)` for
every affine open `W` (`x_1` being the coordinate of index `0`). For every ideal sheaf `I` and
`0 ≤ j ≤ s`,
`D^{s-j}(-log S)(D^j(I)) = ∑_{i=0}^j D^{s-i}(-log S)(∂^i_{x_1} I)`. -/
@[mmp "lem_kr3d_log_derivative_local_decomposition"]
theorem higherLogDerivativeIdeal_higherDerivativeIdeal_eq_iSup [Smooth sX] {n : ℕ}
    {x : Fin (n + 1) → Γ(X, ⊤)} (hx : IsLocalCoordinatesOn sX ⊤ x) (S : X.IdealSheafData)
    (hS : ∀ W : X.affineOpens, S.ideal W = Ideal.span {restrictSection W le_top (x 0)})
    (I : X.IdealSheafData) {j s : ℕ} (hjs : j ≤ s) :
    higherLogDerivativeIdeal sX S (higherDerivativeIdeal sX I j) (s - j) =
      ⨆ i ∈ Finset.range (j + 1),
        higherLogDerivativeIdeal sX S (partialDerivativeIdeal sX hx 0 I i) (s - i) := by
  have hD : derivativeIdeal sX = (partialFamily hx).sheaf :=
    funext (derivativeIdeal_eq_partialFamily hx)
  have hDL : logDerivativeIdeal sX S = (logFamily hx).sheaf :=
    funext (logDerivativeIdeal_eq_logFamily hx S hS)
  have hP : (fun J' : X.IdealSheafData => sInf {J'' : X.IdealSheafData |
      ∀ (W : X.affineOpens), ∀ f ∈ J'.ideal W,
        partialDerivative hx W le_top 0 f ∈ J''.ideal W}) = (firstFamily hx).sheaf :=
    funext (firstStep_eq hx)
  change (logDerivativeIdeal sX S)^[s - j] ((derivativeIdeal sX)^[j] I) =
    ⨆ i ∈ Finset.range (j + 1), (logDerivativeIdeal sX S)^[s - i]
      ((fun J' : X.IdealSheafData => sInf {J'' : X.IdealSheafData |
        ∀ (W : X.affineOpens), ∀ f ∈ J'.ideal W,
          partialDerivative hx W le_top 0 f ∈ J''.ideal W})^[i] I)
  rw [hD, hDL, hP]
  exact iterate_log_derivative_eq_iSup (partialFamily hx).sheaf (logFamily hx).sheaf
    (firstFamily hx).sheaf (logFamily hx).sheaf_mono (firstFamily hx).sheaf_mono
    (logFamily hx).sheaf_biSup (firstFamily hx).sheaf_biSup (partialFamily_sheaf_eq hx)
    (le_firstFamily_sheaf hx) (firstFamily_logFamily_le hx) I hjs

/-- **Kollár (3.87.2)**, the case `j = s`. Let `X` be smooth over `k`, `S ⊆ X` a hypersurface
and `x_1, …, x_n` local coordinates on `X` with `S = (x_1 = 0)`. For every ideal sheaf `I` and
`s ≥ 0`, `D^s(I) = ∑_{i=0}^s D^{s-i}(-log S)(∂^i_{x_1} I)`. -/
@[mmp "lem_kr3d_log_derivative_local_decomposition"]
theorem higherDerivativeIdeal_eq_iSup_higherLogDerivativeIdeal [Smooth sX] {n : ℕ}
    {x : Fin (n + 1) → Γ(X, ⊤)} (hx : IsLocalCoordinatesOn sX ⊤ x) (S : X.IdealSheafData)
    (hS : ∀ W : X.affineOpens, S.ideal W = Ideal.span {restrictSection W le_top (x 0)})
    (I : X.IdealSheafData) (s : ℕ) :
    higherDerivativeIdeal sX I s =
      ⨆ i ∈ Finset.range (s + 1),
        higherLogDerivativeIdeal sX S (partialDerivativeIdeal sX hx 0 I i) (s - i) := by
  have h := higherLogDerivativeIdeal_higherDerivativeIdeal_eq_iSup hx S hS I (le_refl s)
  rwa [Nat.sub_self, higherLogDerivativeIdeal_zero] at h

end LogDecomposition

end MMP.Resolution.Kollar
