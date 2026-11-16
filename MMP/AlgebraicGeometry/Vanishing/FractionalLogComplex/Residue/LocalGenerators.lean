module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Residue.Defs

/-!
# Local generators of `C^0` along a single component of `D`

Let `D` be a relative simple normal crossing divisor, `M` a Cartier divisor, `N M = Bn + div ψ`
and `u = ψ` on `U' = X ∖ (D ∪ Supp M)`. Let `E` be a component of `D` and `W` an open meeting
no other component of `D`. Near every point of `W` the sheaf `𝒪_X(-M)` has a generator `g₀`
with `g₀^N = u · v · t^{Bn(E)}` on `U ∩ W' ∩ U'`, where `t` is a local equation of `E` and `v` is
a function invertible off `D ∪ Supp M`, and every section of `C^0 = 𝒪_X(-M)(-S)` is, locally,
`g₀ H` with `H` regular. These are the local data of the residue computation for the connection
`∇ = d - (N u)⁻¹ du` of `C^•`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_prod_pow_eq_pow_mul`: a monomial in the
  coordinates of a chart, on an open meeting only one of its components.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_residue_chart`: the generator `g₀` and the
  factorization `g₀^N = u · v · t^{Bn(E)}`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_incl_zero_eq_sm_mul`: a section of `C^0` is
  locally `g₀ H`.
-/

universe u

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MMP.Mori

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

variable {X : Scheme.{u}}

/-- A local equation of a prime divisor `P` on `W₂` restricts to a unit on an affine open
`W' ⊆ W₂` disjoint from `P`. -/
theorem isUnit_map_of_disjoint {P : MMP.Mori.PrimeDivisor X} {W₂ W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ W₂) {τ : Γ(X, W₂)} (hτ : P.idealSheaf.ideal W₂ = Ideal.span {τ})
    (h : ∀ y ∈ (W' : X.Opens), y ∉ P.support) :
    IsUnit (X.presheaf.map (homOfLE hW').op τ) := by
  have e := P.idealSheaf.map_ideal (show W' ≤ W₂ from hW')
  rw [hτ, Ideal.map_span, Set.image_singleton] at e
  exact Ideal.span_singleton_eq_top.mp (e.trans (ideal_eq_top_of_disjoint _ W' h))

/-- **The monomial of a chart near one component.** On a chart `W₂` of `D` with coordinates
`τₖ` cutting out the components `jₖ`, and an affine `W' ⊆ W₂` meeting no component of `D` other
than `E`, the monomial `∏ τₖ^{B(jₖ)}` is `σ^{B(E)} q` on `W'`, with `σ` a local equation of `E`
on `W'` and `q` a unit. -/
theorem exists_prod_pow_eq_pow_mul (D : Divisor X) {W₂ W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ W₂) {r : ℕ} (τ : Fin r → Γ(X, W₂)) (j : Fin r → MMP.Mori.PrimeDivisor X)
    (hj : Function.Injective j) (hjD : ∀ k, j k ∈ D.support)
    (hτ : ∀ k, (j k).idealSheaf.ideal W₂ = Ideal.span {τ k})
    (hDW₂ : D.suppIdeal.ideal W₂ = Ideal.span {∏ k, τ k})
    {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ D.support)
    (hmiss : ∀ E' ∈ D.support, E' ≠ E → ∀ y ∈ (W' : X.Opens), y ∉ E'.support)
    (B : MMP.Mori.PrimeDivisor X → ℕ) :
    ∃ σ q : Γ(X, W'), E.idealSheaf.ideal W' = Ideal.span {σ} ∧ IsUnit q ∧
      X.presheaf.map (homOfLE hW').op (∏ k, τ k ^ B (j k)) = σ ^ B E * q := by
  classical
  have hunit : ∀ k, j k ≠ E → IsUnit (X.presheaf.map (homOfLE hW').op (τ k)) := fun k hk =>
    isUnit_map_of_disjoint hW' (hτ k) (hmiss _ (hjD k) hk)
  simp only [map_prod, map_pow]
  by_cases h : ∃ k₀, j k₀ = E
  · obtain ⟨k₀, rfl⟩ := h
    refine ⟨X.presheaf.map (homOfLE hW').op (τ k₀),
      ∏ k ∈ Finset.univ.erase k₀, X.presheaf.map (homOfLE hW').op (τ k) ^ B (j k), ?_,
      IsUnit.prod_iff.mpr fun k hk => (hunit k fun e => (Finset.ne_of_mem_erase hk) (hj e)).pow _,
      (Finset.mul_prod_erase _ _ (Finset.mem_univ k₀)).symm⟩
    have e := (j k₀).idealSheaf.map_ideal (show W' ≤ W₂ from hW')
    rw [hτ, Ideal.map_span, Set.image_singleton] at e
    exact e.symm
  · push Not at h
    refine ⟨1, ∏ k, X.presheaf.map (homOfLE hW').op (τ k) ^ B (j k), ?_,
      IsUnit.prod_iff.mpr fun k _ => (hunit k (h k)).pow _, by rw [one_pow, one_mul]⟩
    rw [Ideal.span_singleton_one]
    refine ideal_eq_top_of_disjoint _ W' fun y hy hyE => ?_
    obtain ⟨k, hk⟩ := exists_eq_of_mem_chart τ le_rfl j hτ hDW₂ hE (hW' hy) hyE
    exact h k hk

/-- **A generator of `𝒪_X(-M)` along a single component.** Let `E` be a component of `D` and `W`
an open meeting no other component of `D`. Near every point `y` there are an affine `W₂` and a
generator `g₀` of `𝒪_X(-M)` on every open of `W₂` such that, on every affine `W' ⊆ W ∩ W₂` with
a local equation `t` of `E`, `g₀^N = u · v · t^{Bn(E)}` on `U ∩ W' ∩ U'`, with `v` a function on
`W'` which is invertible on `U ∩ W' ∩ U'`, of inverse `vi`; there `t` is a unit. -/
theorem exists_residue_chart (n : ℕ) {T : Scheme.{u}} (f : X ⟶ T)
    [SmoothOfRelativeDimension n f] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (D : Divisor X) (hD : D.IsRelativeSNC n f) (M : Divisor X) (uu : Γ(X, cU' D M))
    (hMC : M.IsCartier) (Bn : Divisor X) (N : ℕ) (ψ : (RationalFunctions X)ˣ)
    (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (hu : (toRationalFunctionsPresheaf X).app (op (cU' D M)) uu = ratRes (cU' D M) ψ)
    (hBn : ∀ E, 0 ≤ Bn E) (hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support)
    {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ D.support) {W : X.Opens}
    (hmiss : ∀ E' ∈ D.support, E' ≠ E → ∀ y ∈ W, y ∉ E'.support) (y : X) :
    ∃ (W₂ : X.affineOpens) (_ : y ∈ (W₂ : X.Opens)) (g₀ : Γ(X, (W₂ : X.Opens) ⊓ cU' D M)),
      DivCond (D := D) (M := M) (W₂ : X.Opens) g₀ ∧
      (∀ (W₃ : X.Opens) (h₃ : W₃ ≤ W₂) (g : Γ(X, W₃ ⊓ cU' D M)), DivCond (D := D) (M := M) W₃ g →
        ∃ h : Γ(X, W₃), g = X.presheaf.map (homOfLE inf_le_left).op h *
          X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g₀) ∧
      ∀ (W' : X.affineOpens) (hW₂ : (W' : X.Opens) ≤ W₂), (W' : X.Opens) ≤ W →
        ∀ t : Γ(X, W'), E.idealSheaf.ideal W' = Ideal.span {t} →
        ∃ v vi : Γ(X, W'), resO D M W' vi * resO D M W' v = 1 ∧ IsUnit (resO D M W' t) ∧
          ((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M)).hom
              (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW₂)).op g₀) ^ N =
            resU W' uu * resO D M W' v * resO D M W' t ^ (Bn E).toNat := by
  classical
  obtain ⟨W₂, hy₂, r, τ, j, v₀, g₀, hj, hjD, hτ, hDW₂, hv₀, hg₀div, hg₀gen, hX⟩ :=
    exists_generator_factorization n f D hD M uu hMC Bn N ψ hψ hu hBn hBD y
  refine ⟨W₂, hy₂, g₀, hg₀div, hg₀gen, fun W' hW₂ hW t ht => ?_⟩
  obtain ⟨σ, q, hσ, hq, hprod⟩ := exists_prod_pow_eq_pow_mul D hW₂ τ j hj hjD hτ hDW₂ hE
    (fun E' hE' hne y hy => hmiss E' hE' hne y (hW hy)) (fun P => (Bn P).toNat)
  have hσt : Ideal.span {σ} = Ideal.span {t} := hσ.symm.trans ht
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hσt ▸ Ideal.mem_span_singleton_self σ)
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp (hσt.symm ▸ Ideal.mem_span_singleton_self t)
  set ρ : Γ(X, (W' : X.Opens)) →+* Γ((cU D).toScheme, OO D M W') :=
    ((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M)).hom.comp (X.presheaf.map (homOfLE inf_le_left).op).hom
  have hρ : ∀ c, resO D M W' c = ρ c := fun _ => rfl
  have htu : IsUnit (ρ t) := by
    rw [show ρ t = _ from (G1.app_restrict (U := cU D)
      (inf_le_left : (W' : X.Opens) ⊓ cU' D M ≤ W') t).symm]
    exact (B1.isUnit_res_of_ideal_eq D hE ht).map
      ((cU D).toScheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
        (inf_le_left : (W' : X.Opens) ⊓ cU' D M ≤ W'))).op).hom
  have haa : ρ a * ρ a' = 1 := htu.mul_left_cancel <| by
    rw [mul_one]
    calc ρ t * (ρ a * ρ a') = ρ (a' * (a * t)) := by
          rw [map_mul, map_mul]
          ring
      _ = ρ t := by rw [ha, ha']
  obtain ⟨v₀i, hv₀i⟩ := (hv₀.map (X.presheaf.map (homOfLE hW₂).op).hom).exists_left_inv
  obtain ⟨qi, hqi⟩ := hq.exists_left_inv
  refine ⟨X.presheaf.map (homOfLE hW₂).op v₀ * q * a ^ (Bn E).toNat,
    v₀i * qi * a' ^ (Bn E).toNat, ?_, htu, ?_⟩
  · rw [hρ, hρ, ← map_mul]
    calc ρ (v₀i * qi * a' ^ (Bn E).toNat * (X.presheaf.map (homOfLE hW₂).op v₀ * q *
          a ^ (Bn E).toNat)) =
        ρ (v₀i * X.presheaf.map (homOfLE hW₂).op v₀) * ρ (qi * q) *
          (ρ a * ρ a') ^ (Bn E).toNat := by
          simp only [map_mul, map_pow]
          ring
      _ = 1 := by rw [hv₀i, hqi, haa, map_one, one_pow, one_mul, one_mul]
  · set b := (Bn E).toNat
    have e1 : X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW₂)).op
        (X.presheaf.map (homOfLE inf_le_right).op uu) =
        X.presheaf.map (homOfLE inf_le_right).op uu := presheaf_map_map _ _ _ uu
    have e2 : X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW₂)).op
        (X.presheaf.map (homOfLE inf_le_left).op (v₀ * ∏ k, τ k ^ (Bn (j k)).toNat)) =
        X.presheaf.map (homOfLE inf_le_left).op (X.presheaf.map (homOfLE hW₂).op
          (v₀ * ∏ k, τ k ^ (Bn (j k)).toNat)) :=
      (presheaf_map_map _ _ (homOfLE (inf_le_left.trans hW₂)).op _).trans
        (presheaf_map_map _ _ _ _).symm
    have e3 : X.presheaf.map (homOfLE hW₂).op (v₀ * ∏ k, τ k ^ (Bn (j k)).toNat) =
        X.presheaf.map (homOfLE hW₂).op v₀ * q * a ^ b * t ^ b := by
      rw [map_mul, hprod, ← ha]
      ring
    calc ((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M)).hom
          (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW₂)).op g₀) ^ N =
        ((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M)).hom
          (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW₂)).op (g₀ ^ N)) := by
          rw [map_pow, map_pow]
      _ = ((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M)).hom
          (X.presheaf.map (homOfLE inf_le_right).op uu *
            X.presheaf.map (homOfLE inf_le_left).op
              (X.presheaf.map (homOfLE hW₂).op v₀ * q * a ^ b * t ^ b)) := by
          rw [hX, map_mul, e1, e2, e3]
      _ = _ := by
          rw [map_mul, map_mul, map_mul, map_pow, map_pow, ← mul_assoc]

/-- **A section of `C^0` is a multiple of the generator.** If `ω` is a section of
`C^0 = 𝒪_X(-M)(-S)` over `W` and `g₀` generates `𝒪_X(-M)` on every open of `W₂`, then near every
point `y` of `W ∩ W₂` there is an affine `W'` on which `ω = g₀ H` with `H` a function on `W'`. -/
theorem exists_incl_zero_eq_sm_mul (n : ℕ) {T : Scheme.{u}} (f : X ⟶ T)
    [SmoothOfRelativeDimension n f] [IsLocallyNoetherian X] [IsNormal X]
    (D : Divisor X) (hD : D.IsRelativeSNC n f) (S M : Divisor X) {W : X.Opens}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece ((0 : ℕ) : ℤ)).val.obj
      (op (OO D M W))} (hω : Cond n f D hD S M 0 W ω) {y : X} (hy : y ∈ W)
    {W₂ : X.Opens} (hy₂ : y ∈ W₂) (g₀ : Γ(X, W₂ ⊓ cU' D M))
    (hgen : ∀ (W₃ : X.Opens) (h₃ : W₃ ≤ W₂) (g : Γ(X, W₃ ⊓ cU' D M)),
      DivCond (D := D) (M := M) W₃ g → ∃ h : Γ(X, W₃),
        g = X.presheaf.map (homOfLE inf_le_left).op h *
          X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g₀) :
    ∃ (W' : X.affineOpens) (h : (W' : X.Opens) ≤ W) (h₂ : (W' : X.Opens) ≤ W₂),
      y ∈ (W' : X.Opens) ∧ ∃ H : Γ(X, (W' : X.Opens)),
        (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) (rO f (D := D) (M := M) ((0 : ℕ) : ℤ) h ω) =
          sm ((cU D).ι ≫ f) (OO D M W') (((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M)).hom
            (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₂)).op g₀) *
              resO D M W' H) := by
  classical
  obtain ⟨W₁, h₁, hy₁, m, g, η, hg, hη, he⟩ := hω y hy
  choose W'' hle hy'' c hc hce using fun i =>
    B1.exists_res_of_mem_relativeLogForms_zero f D n hD S.suppIdeal (hη i) hy₁
  obtain ⟨W', hy', hW'₀, hW''⟩ := exists_affine_forall Finset.univ
    (fun i (Z : X.Opens) => Z ≤ W'' i) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun i _ => ⟨W'' i, hy'' i, le_rfl⟩) ((W₁ : X.Opens) ⊓ W₂) ⟨hy₁, hy₂⟩
  have k₁ : (W' : X.Opens) ≤ W₁ := hW'₀.trans inf_le_left
  have k₂ : (W' : X.Opens) ≤ W₂ := hW'₀.trans inf_le_right
  have k'' : ∀ i, (W' : X.Opens) ≤ W'' i := fun i => hW'' i (Finset.mem_univ i)
  have he₃ := (congrArg ((TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ))
    (rO_rO f (D := D) (M := M) ((0 : ℕ) : ℤ) h₁ k₁ ω)).symm.trans
      (sum_rep_restrict f D M k₁ g η he)
  choose hh hhe using fun i => hgen W' k₂ _ (DivCond.restrict D M k₁ (hg i))
  refine ⟨W', k₁.trans h₁, k₂, hy',
    ∑ i, hh i * X.presheaf.map (homOfLE (k'' i)).op (c i), he₃.trans ?_⟩
  have hi : ∀ i, (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
        ((0 : ℕ) : ℤ)).val.map (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
          (inf_le_left.trans k₁))).op (η i)) =
      sm ((cU D).ι ≫ f) (OO D M W') (resO D M W' (X.presheaf.map (homOfLE (k'' i)).op (c i))) := by
    intro i
    have hψ : (W' : X.Opens) ⊓ cU' D M ≤ W'' i := inf_le_left.trans (k'' i)
    have e1 := congrArg ((TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ))
      (piece_map_map _ ((Opens.map (cU D).ι.base).map (homOfLE (hle i))).op
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι hψ)).op
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans k₁))).op (η i))
    have e2 := incl_map f D (homOfLE (Scheme.Hom.preimage_mono (cU D).ι hψ)).op ((0 : ℕ) : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
        ((0 : ℕ) : ℤ)).val.map ((Opens.map (cU D).ι.base).map (homOfLE (hle i))).op (η i))
    refine (e1.symm.trans e2).trans ?_
    refine (congrArg _ (hce i)).trans ?_
    refine (totalRestrict_sm _ _).trans ?_
    exact congrArg _ ((G1.app_restrict hψ (c i)).trans
      (congrArg _ (presheaf_map_map _ _ _ _).symm))
  refine (Finset.sum_congr rfl fun i _ => by rw [hi i, hhe i]).trans ?_
  change ∑ i, sm ((cU D).ι ≫ f) (OO D M W') _ * _ = _
  simp only [← map_mul, ← map_sum]
  refine congrArg _ ?_
  simp only [map_mul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end MMP.FourfoldProofs.FractionalLogComplexProof
