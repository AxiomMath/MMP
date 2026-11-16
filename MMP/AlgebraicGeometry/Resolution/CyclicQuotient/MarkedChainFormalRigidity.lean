module
public import MMP.AlgebraicGeometry.Resolution.CyclicQuotient.MarkedChainFormalCharts

/-!
# Formal rigidity of a doubly marked negative chain of rational curves

Let `X` be a smooth surface over an algebraically closed field `K` of characteristic zero and
`E = E₀ + ⋯ + E_{r-1}` a chain of smooth rational curves on `X` with simple normal crossings and
`Eᵢ² = -bᵢ`, `2 ≤ bᵢ`, whose two ends are marked by smooth formal curve germs transverse to `E₀`
and `E_{r-1}`, away from the other components and at distinct points. Then the formal completion of
`X` along `E`, together with its two markings, is isomorphic to the *formal plumbing* of the
chain: the formal scheme glued from `r + 1` copies of the completion of `𝔸²_K` along the
exceptional axes, with coordinates `(xⱼ, yⱼ)`, along the monomial transitions
`xⱼ = x_{j-1}^{bⱼ} y_{j-1}`, `yⱼ = x_{j-1}⁻¹`. In these charts the exceptional ideal is `(y₀)`,
`(xⱼ yⱼ)` and `(x_r)`, and the two markings are `(x₀)` and `(y_r)`.

## Main results

* `MMP.Mori.exists_formalPlumbingCharts_of_isSNCChain`: the completion along a doubly marked
  chain with all `bᵢ ≥ 2` is covered by formal coordinate charts whose transitions are exactly
  the monomial plumbing transitions, at every finite level.

## Implementation notes

*The formal plumbing.* The isomorphism with the formal plumbing is stated chart by chart: the
completion is covered by `r + 1` formal opens, each identified with the completion of `𝔸²_K`
along its exceptional ideal by a pair of formal coordinates `(xⱼ, yⱼ)`; consecutive charts meet
exactly where `x_{j-1}`, equivalently `yⱼ`, is invertible; non-consecutive charts do not meet;
and on each overlap the coordinates satisfy `yⱼ x_{j-1} = 1` and `xⱼ = x_{j-1}^{bⱼ} y_{j-1}` on
every thickening. Gluing the chart identifications along these overlaps is the isomorphism of
the completion with the plumbing, and conversely an isomorphism with the plumbing restricts to
such charts.

*The formal completion.* The completion `X̂` of `X` along `E` is the colimit of the
thickenings `(n+1)E`, the closed subschemes cut out by the powers `I_E ^ (n + 1)` of the ideal
`I_E = ∏ᵢ I_{Eᵢ}`. A formal function on the formal open over an open `V ⊆ X` is a compatible
family of sections of the thickenings over `V`, and a formal chart isomorphic to the completion
of `𝔸²_K` along the ideal `J` is a pair of such families `(x, y)` such that, at every level, the
thickening over `V` is affine and `K[X₀, X₁] → Γ((n+1)E, V)`, `X₀ ↦ x`, `X₁ ↦ y`, is
surjective with kernel `J ^ (n + 1)`.

*The markings.* A smooth formal curve germ `D̂` at `p` transverse to `E` is recorded by its
traces `Zₙ = D̂ ∩ (n+1)E`: closed subschemes `Zₙ ⊆ (n+1)E` with `Zₙ = Zₙ₊₁ ∩ (n+1)E`,
`Z₀ = {p}` and `Zₙ ≅ Spec K[t]/(t^(n+1))` over `K`. In particular the two markings may be two
formal branches of one algebraic curve.

*The chain.* The chain condition is recorded by intersection numbers: on a smooth surface,
`(Eᵢ · Eᵢ₊₁) = 1` says that consecutive components meet transversally in exactly one point,
and non-consecutive components are disjoint.
-/

section

universe u v w

open AlgebraicGeometry CategoryTheory Opposite MMP.Mori
open LaurentPolynomial

namespace Proof_lem_mmp_foundation_marked_negative_chain_formal_rigidity

section Defs

variable {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (I : X.IdealSheafData)

/-- The `(n+1)`-st thickening. -/
private noncomputable abbrev Sc (n : ℕ) : Scheme.{u} := (I ^ (n + 1)).subscheme

private noncomputable abbrev trc (n : ℕ) (V : X.Opens) : (Sc I n).Opens :=
  (I ^ (n + 1)).subschemeι ⁻¹ᵁ V

private noncomputable def sigc (n : ℕ) (U : (Sc I n).Opens) : K →+* Γ(Sc I n, U) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫
    ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U le_top).hom

private noncomputable def rhoc (n : ℕ) (V : X.Opens) :
    Γ(Sc I (n + 1), trc I (n + 1) V) →+* Γ(Sc I n, trc I n V) :=
  ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
      (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (trc I (n + 1) V) (trc I n V)
    (by
      simp only [trc, ← Scheme.Hom.comp_preimage,
        Scheme.IdealSheafData.inclusion_subschemeι, le_refl])).hom

private noncomputable def resc (n : ℕ) (V W : X.Opens) (h : W ≤ V) :
    Γ(Sc I n, trc I n V) →+* Γ(Sc I n, trc I n W) :=
  ((Sc I n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom

private noncomputable def Jc (r : ℕ) : Fin (r + 1) → Ideal (MvPolynomial (Fin 2) K) := fun j =>
  if j = 0 then Ideal.span {MvPolynomial.X 1}
  else if j = Fin.last r then Ideal.span {MvPolynomial.X 0}
  else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}

variable {r : ℕ} (V : Fin (r + 1) → X.Opens)

/-- Chart `j` is the completion of `𝔸²` along `Jc j`, at level `m`. -/
private def PresAt (m : ℕ) (xm ym : ∀ j, Γ(Sc I m, trc I m (V j))) : Prop :=
  ∀ j, IsAffineOpen (trc I m (V j)) ∧
    Function.Surjective (MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V j))) ![xm j, ym j]) ∧
    RingHom.ker (MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V j))) ![xm j, ym j]) =
      Jc r j ^ (m + 1)

/-- The markings at level `m`. -/
private def MarkAt (ZL ZR : ℕ → X.IdealSheafData) (hZL : ∀ n, I ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, I ^ (n + 1) ≤ ZR n) (m : ℕ) (xm ym : ∀ j, Γ(Sc I m, trc I m (V j))) : Prop :=
  RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL m)).app (trc I m (V 0))).hom =
      Ideal.span {xm 0} ∧
    RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR m)).app
      (trc I m (V (Fin.last r)))).hom = Ideal.span {ym (Fin.last r)}

/-- The overlaps at level `m`. -/
private def OvAt (m : ℕ) (xm ym : ∀ j, Γ(Sc I m, trc I m (V j))) : Prop :=
  ∀ j : Fin r, trc I m (V j.castSucc ⊓ V j.succ) = (Sc I m).basicOpen (xm j.castSucc) ∧
    trc I m (V j.castSucc ⊓ V j.succ) = (Sc I m).basicOpen (ym j.succ)

/-- `y_{j+1} x_j = 1` at level `m`. -/
private def TransYAt (m : ℕ) (xm ym : ∀ j, Γ(Sc I m, trc I m (V j))) : Prop :=
  ∀ j : Fin r, resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (ym j.succ) *
    resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (xm j.castSucc) = 1

/-- `x_{j+1} = x_j ^ b_j y_j` at level `m`. -/
private def TransXAt (b : Fin r → ℕ) (m : ℕ) (xm ym : ∀ j, Γ(Sc I m, trc I m (V j))) : Prop :=
  ∀ j : Fin r, resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (xm j.succ) =
    resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (xm j.castSucc) ^ b j *
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (ym j.castSucc)

/-- Compatibility of consecutive levels. -/
private def CompatAt (n : ℕ) (xn1 : ∀ j, Γ(Sc I (n + 1), trc I (n + 1) (V j)))
    (xn : ∀ j, Γ(Sc I n, trc I n (V j))) : Prop :=
  ∀ j, rhoc I n (V j) (xn1 j) = xn j

/-- The corrected charts are good up to level `N`. -/
private def GoodUpTo (ZL ZR : ℕ → X.IdealSheafData) (hZL : ∀ n, I ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, I ^ (n + 1) ≤ ZR n) (b : Fin r → ℕ) (N : ℕ)
    (x y : ∀ j m, Γ(Sc I m, trc I m (V j))) : Prop :=
  (∀ m ≤ N, PresAt sX I V m (fun j => x j m) (fun j => y j m) ∧
    MarkAt I V ZL ZR hZL hZR m (fun j => x j m) (fun j => y j m) ∧
    OvAt I V m (fun j => x j m) (fun j => y j m) ∧
    TransYAt I V m (fun j => x j m) (fun j => y j m) ∧
    TransXAt I V b m (fun j => x j m) (fun j => y j m)) ∧
  (∀ m < N, CompatAt I V m (fun j => x j (m + 1)) (fun j => x j m) ∧
    CompatAt I V m (fun j => y j (m + 1)) (fun j => y j m))

end Defs

private lemma seq_limit {ι : Type v} {T : ι → ℕ → Type w}
    (P : ℕ → (∀ i m, T i m) → (∀ i m, T i m) → Prop)
    (hloc : ∀ n x y x' y', (∀ i m, m ≤ n → x i m = x' i m ∧ y i m = y' i m) →
      P n x y → P n x' y')
    (base : ∃ x y, P 0 x y)
    (ext : ∀ n, ∀ x y, P n x y → ∃ x' y', P (n + 1) x' y' ∧
      ∀ i m, m ≤ n → x' i m = x i m ∧ y' i m = y i m) :
    ∃ x y, ∀ n, P n x y := by
  classical
  let S : ℕ → Type _ := fun k => {p : (∀ i m, T i m) × (∀ i m, T i m) // P k p.1 p.2}
  let step : ∀ k, S k → S (k + 1) := fun k s =>
    ⟨(Classical.choose (ext k s.1.1 s.1.2 s.2),
      Classical.choose (Classical.choose_spec (ext k s.1.1 s.1.2 s.2))),
      (Classical.choose_spec (Classical.choose_spec (ext k s.1.1 s.1.2 s.2))).1⟩
  have step_agree : ∀ k (s : S k), ∀ i m, m ≤ k →
      (step k s).1.1 i m = s.1.1 i m ∧ (step k s).1.2 i m = s.1.2 i m := fun k s =>
    (Classical.choose_spec (Classical.choose_spec (ext k s.1.1 s.1.2 s.2))).2
  obtain ⟨x0, y0, h0⟩ := base
  let seq : ∀ k, S k := fun k => Nat.rec ⟨(x0, y0), h0⟩ step k
  have hA : ∀ a b, a ≤ b → ∀ i m, m ≤ a →
      (seq b).1.1 i m = (seq a).1.1 i m ∧ (seq b).1.2 i m = (seq a).1.2 i m := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact fun _ _ _ => ⟨rfl, rfl⟩
    | succ b hab ih =>
      intro i m hm
      have := step_agree b (seq b) i m (by omega)
      exact ⟨this.1.trans (ih i m hm).1, this.2.trans (ih i m hm).2⟩
  refine ⟨fun i m => (seq m).1.1 i m, fun i m => (seq m).1.2 i m, fun n => ?_⟩
  refine hloc n (seq n).1.1 (seq n).1.2 _ _ ?_ (seq n).2
  exact fun i m hm => hA m n hm i m le_rfl

section Alg

variable {K : Type u} [Field K]

private lemma presentation_mul_unit {A : Type u} [CommRing A]
    (σ : K →+* A) (x y u v : A) (J : Ideal (MvPolynomial (Fin 2) K)) (g : MvPolynomial (Fin 2) K)
    (hJ : J = Ideal.span {g}) (hg : g = MvPolynomial.X 1 ∨ g = MvPolynomial.X 0 * MvPolynomial.X 1
        ∨ g = MvPolynomial.X 0) (k : ℕ)
    (hker : RingHom.ker (MvPolynomial.eval₂Hom σ ![x, y]) = J ^ k)
    (pu pv : MvPolynomial (Fin 2) K) (hu : pu - 1 ∈ J) (hv : pv - 1 ∈ J)
    (heu : MvPolynomial.eval₂Hom σ ![x, y] pu = u) (hev : MvPolynomial.eval₂Hom σ ![x, y] pv = v) :
    RingHom.ker (MvPolynomial.eval₂Hom σ ![x * u, y * v]) = J ^ k ∧
      (Function.Surjective (MvPolynomial.eval₂Hom σ ![x, y]) →
        Function.Surjective (MvPolynomial.eval₂Hom σ ![x * u, y * v])) := by
  classical
  set ev := MvPolynomial.eval₂Hom σ ![x, y] with hev0
  let θ : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
    MvPolynomial.aeval ![MvPolynomial.X 0 * pu, MvPolynomial.X 1 * pv]
  have hcomp : MvPolynomial.eval₂Hom σ ![x * u, y * v] = ev.comp θ.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp [θ, ev]
    · have heu' : MvPolynomial.eval₂ σ ![x, y] pu = u := heu
      have hev' : MvPolynomial.eval₂ σ ![x, y] pv = v := hev
      fin_cases i <;> simp [θ, ev, heu', hev']
  -- `θ` is the identity modulo `J`
  have hmod : ∀ h, θ h - h ∈ J := by
    intro h
    have : (Ideal.Quotient.mk J).comp θ.toRingHom = Ideal.Quotient.mk J := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · simp [θ]
      · have h1 : Ideal.Quotient.mk J pu = 1 := by
          rw [← map_one (Ideal.Quotient.mk J)]
          exact (Ideal.Quotient.eq).2 hu
        have h2 : Ideal.Quotient.mk J pv = 1 := by
          rw [← map_one (Ideal.Quotient.mk J)]
          exact (Ideal.Quotient.eq).2 hv
        fin_cases i <;> simp [θ, h1, h2]
    exact (Ideal.Quotient.eq).1 (by simpa using congrArg (fun F => F h) this)
  -- `θ g = g * w` with `w ≡ 1 (mod J)`
  obtain ⟨w, hw, hwJ⟩ : ∃ w, θ g = g * w ∧ w - 1 ∈ J := by
    rcases hg with rfl | rfl | rfl
    · exact ⟨pv, by simp [θ, mul_comm], hv⟩
    · refine ⟨pu * pv, by simp [θ]; ring, ?_⟩
      rw [show pu * pv - 1 = (pu - 1) * pv + (pv - 1) by ring]
      exact J.add_mem (J.mul_mem_right _ hu) hv
    · exact ⟨pu, by simp [θ, mul_comm], hu⟩
  have hpowJ : ∀ i : ℕ, ∀ f, f ∈ J ^ i → θ f - f ∈ J ^ (i + 1) := by
    intro i f hf
    rw [hJ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hf
    obtain ⟨h, rfl⟩ := hf
    have h1 : w ^ i - 1 ∈ J := by
      have : Ideal.Quotient.mk J w = 1 := by
        rw [← map_one (Ideal.Quotient.mk J)]; exact (Ideal.Quotient.eq).2 hwJ
      exact (Ideal.Quotient.eq).1 (by rw [map_pow, this, one_pow, map_one])
    have e : θ (g ^ i * h) - g ^ i * h = g ^ i * ((w ^ i - 1) * θ h + (θ h - h)) := by
      rw [map_mul, map_pow, hw, mul_pow]; ring
    rw [e, pow_succ]
    refine Ideal.mul_mem_mul ?_ (J.add_mem (J.mul_mem_right _ h1) (hmod h))
    rw [hJ]; exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self g) i
  let θl : Module.End K (MvPolynomial (Fin 2) K) := θ.toLinearMap
  let D : Module.End K (MvPolynomial (Fin 2) K) := θl - 1
  have hD : ∀ j : ℕ, ∀ f, f ∈ J ^ j → (-D) f ∈ J ^ (j + 1) := by
    intro j f hf
    simpa [D, θl] using (J ^ (j + 1)).neg_mem (hpowJ j f hf)
  have hDn : ∀ i j : ℕ, ∀ f, f ∈ J ^ j → ((-D) ^ i) f ∈ J ^ (j + i) := by
    intro i
    induction i with
    | zero => intro j f hf; simpa using hf
    | succ i ih =>
      intro j f hf
      have := hD _ _ (ih j f hf)
      rw [pow_succ', Module.End.mul_apply]
      simpa [add_assoc] using this
  have e : θl = 1 - (-D) := by simp [D]
  have hgeom : θl * ∑ i ∈ Finset.range k, (-D) ^ i = 1 - (-D) ^ k := by
    rw [e]
    exact mul_neg_geom_sum (-D) k
  have hgeom' : (∑ i ∈ Finset.range k, (-D) ^ i) * θl = 1 - (-D) ^ k := by
    rw [e]
    exact geom_sum_mul_neg (-D) k
  have hS : ∀ f, f ∈ J ^ k → (∑ i ∈ Finset.range k, (-D) ^ i) f ∈ J ^ k := by
    intro f hf
    rw [LinearMap.sum_apply]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    exact Ideal.pow_le_pow_right (Nat.le_add_right k i) (hDn i k f hf)
  have hrem : ∀ f, ((-D) ^ k) f ∈ J ^ k := fun f => by simpa using hDn k 0 f (by simp)
  have hθS : ∀ f, θ ((∑ i ∈ Finset.range k, (-D) ^ i) f) = f - ((-D) ^ k) f := by
    intro f
    simpa [θl] using congrArg (fun F => F f) hgeom
  have hSθ : ∀ f, (∑ i ∈ Finset.range k, (-D) ^ i) (θ f) = f - ((-D) ^ k) f := by
    intro f
    simpa [θl] using congrArg (fun F => F f) hgeom'
  refine ⟨?_, fun hs a => ?_⟩
  · rw [hcomp]
    ext f
    simp only [RingHom.mem_ker, RingHom.comp_apply]
    constructor
    · intro hf
      have h1 : θ f ∈ J ^ k := by rw [← hker]; exact hf
      have h2 := hS _ h1
      rw [hSθ] at h2
      simpa using (J ^ k).add_mem h2 (hrem f)
    · intro hf
      have h1 : θ f ∈ J ^ k := by
        simpa using (J ^ k).add_mem (Ideal.pow_le_pow_right (Nat.le_succ k) (hpowJ k f hf)) hf
      rwa [← hker] at h1
  · obtain ⟨f, rfl⟩ := hs a
    refine ⟨(∑ i ∈ Finset.range k, (-D) ^ i) f, ?_⟩
    rw [hcomp]
    show ev (θ _) = ev f
    rw [hθS, map_sub]
    have : ev (((-D) ^ k) f) = 0 := by
      rw [← RingHom.mem_ker, hker]; exact hrem f
    rw [this, sub_zero]

end Alg

section AllModel

/-- The model of an overlap ring at level `m`: `K[x^±][y] / (y^(m+1))`. -/
private abbrev Mod (K : Type u) [Field K] (m : ℕ) : Type u :=
  AdjoinRoot ((Polynomial.X : Polynomial (LaurentPolynomial K)) ^ (m + 1))

section

variable {K : Type u} [Field K]

private theorem laurent_hom_ext {S : Type*} [CommRing S] (f g : LaurentPolynomial K →+* S)
    (hC : ∀ k : K, f (LaurentPolynomial.C k) = g (LaurentPolynomial.C k))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  have h1 : (LaurentPolynomial.T (-1) : LaurentPolynomial K) * LaurentPolynomial.T 1 = 1 := by
    rw [← T_add]; simp
  have hTm : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1)) := by
    have e1 : f (LaurentPolynomial.T (-1)) * f (LaurentPolynomial.T 1) = 1 := by
      rw [← map_mul, h1, map_one]
    have e2 : g (LaurentPolynomial.T (-1)) * g (LaurentPolynomial.T 1) = 1 := by
      rw [← map_mul, h1, map_one]
    rw [hT] at e1
    exact left_inv_eq_right_inv e1 ((mul_comm _ _).trans e2)
  refine RingHom.ext fun p => ?_
  refine LaurentPolynomial.induction_on p (fun a => ?_)
    (fun {p q} hp hq => by rw [map_add, map_add, hp, hq]) (fun n a h => ?_) (fun n a h => ?_)
  · exact hC a
  · have : (LaurentPolynomial.C a * LaurentPolynomial.T (n + 1) : LaurentPolynomial K) =
        LaurentPolynomial.C a * LaurentPolynomial.T n * LaurentPolynomial.T 1 := by
      rw [mul_assoc, ← T_add]
    rw [this, map_mul f (LaurentPolynomial.C a * LaurentPolynomial.T n) (LaurentPolynomial.T 1),
      map_mul g (LaurentPolynomial.C a * LaurentPolynomial.T n) (LaurentPolynomial.T 1), h, hT]
  · have : (LaurentPolynomial.C a * LaurentPolynomial.T (-n - 1) : LaurentPolynomial K) =
        LaurentPolynomial.C a * LaurentPolynomial.T (-n) * LaurentPolynomial.T (-1) := by
      rw [mul_assoc, ← T_add]; congr 2
    rw [this, map_mul f (LaurentPolynomial.C a * LaurentPolynomial.T (-n))
      (LaurentPolynomial.T (-1)),
      map_mul g (LaurentPolynomial.C a * LaurentPolynomial.T (-n)) (LaurentPolynomial.T (-1)), h,
          hTm]

private theorem model_level {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (σ : K →+* A)
    (x y : A) (m : ℕ) (J : Ideal (MvPolynomial (Fin 2) K))
    (hJ : J = Ideal.span {MvPolynomial.X 1} ∨ J = Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1})
    (hs : Function.Surjective (MvPolynomial.eval₂Hom σ ![x, y]))
    (hk : RingHom.ker (MvPolynomial.eval₂Hom σ ![x, y]) = J ^ (m + 1))
    [IsLocalization.Away x B] :
    ∃ Θ : Mod K m ≃+* B,
      Θ (AdjoinRoot.of _ (LaurentPolynomial.T 1)) = algebraMap A B x ∧
      Θ (AdjoinRoot.root _) = algebraMap A B y ∧
      ∀ k, Θ (AdjoinRoot.of _ (LaurentPolynomial.C k)) = algebraMap A B (σ k) := by
  classical
  set ev := MvPolynomial.eval₂Hom σ ![x, y] with hev
  have hx : IsUnit (algebraMap A B x) := IsLocalization.Away.algebraMap_isUnit x
  let σB : K →+* B := (algebraMap A B).comp σ
  let Λ : LaurentPolynomial K →+* B := LaurentPolynomial.eval₂ σB hx.unit
  have hΛC : ∀ k : K, Λ (LaurentPolynomial.C k) = σB k := fun k => LaurentPolynomial.eval₂_C _ _ _
  have hΛT : Λ (LaurentPolynomial.T 1) = algebraMap A B x := by
    simp [Λ, LaurentPolynomial.eval₂_T]
  have hy : algebraMap A B y ^ (m + 1) = 0 := by
    rcases hJ with rfl | rfl
    · have : y ^ (m + 1) = 0 := by
        have h : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ (m + 1) ∈
            (Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) ^ (m + 1) := by
          rw [Ideal.span_singleton_pow]; exact Ideal.subset_span rfl
        rw [← hk, RingHom.mem_ker] at h
        simpa [hev] using h
      rw [← map_pow, this, map_zero]
    · have : (x * y) ^ (m + 1) = 0 := by
        have h : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ (m + 1) ∈
            (Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) ^
              (m + 1) := by
          rw [Ideal.span_singleton_pow]; exact Ideal.subset_span rfl
        rw [← hk, RingHom.mem_ker] at h
        simpa [hev] using h
      have h2 := congrArg (algebraMap A B) this
      rw [map_zero, map_pow, map_mul] at h2
      rw [mul_pow] at h2
      exact ((hx.pow (m + 1)).mul_right_eq_zero).1 h2
  let Θ' : Mod K m →+* B := AdjoinRoot.lift Λ (algebraMap A B y) (by simpa using hy)
  have hΘ'of : ∀ c, Θ' (AdjoinRoot.of _ c) = Λ c := fun c => AdjoinRoot.lift_of _
  have hΘ'root : Θ' (AdjoinRoot.root _) = algebraMap A B y := AdjoinRoot.lift_root _
  -- the retraction
  let σM : K →+* Mod K m := (AdjoinRoot.of _).comp (LaurentPolynomial.C : K →+* LaurentPolynomial K)
  have hXm : (AdjoinRoot.root ((Polynomial.X : Polynomial (LaurentPolynomial K)) ^ (m + 1))) ^
      (m + 1) = 0 := by
    simpa using AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial (LaurentPolynomial K)) ^ (m + 1))
  let ψpoly : MvPolynomial (Fin 2) K →+* Mod K m :=
    MvPolynomial.eval₂Hom σM ![AdjoinRoot.of _ (LaurentPolynomial.T 1), AdjoinRoot.root _]
  have hpk : ∀ a ∈ RingHom.ker ev, ψpoly a = 0 := by
    intro a ha
    rw [hk] at ha
    rcases hJ with rfl | rfl
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
      obtain ⟨q, rfl⟩ := ha
      have : ψpoly (MvPolynomial.X 1 ^ (m + 1)) = 0 := by
        rw [map_pow]; simpa [ψpoly] using hXm
      rw [map_mul, this, mul_zero]
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
      obtain ⟨q, rfl⟩ := ha
      have : ψpoly ((MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ (m + 1)) =
          0 := by
        rw [map_pow, map_mul, mul_pow]
        simp only [ψpoly, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hXm, mul_zero]
      rw [map_mul, this, mul_zero]
  let ψA : A →+* Mod K m := (Ideal.Quotient.lift (RingHom.ker ev) ψpoly hpk).comp
    (RingHom.quotientKerEquivOfSurjective hs).symm.toRingHom
  have hψA : ∀ P, ψA (ev P) = ψpoly P := by
    intro P
    have : (RingHom.quotientKerEquivOfSurjective hs).symm (ev P) =
        Ideal.Quotient.mk (RingHom.ker ev) P := by
      rw [RingEquiv.symm_apply_eq]; rfl
    show (Ideal.Quotient.lift (RingHom.ker ev) ψpoly hpk)
      ((RingHom.quotientKerEquivOfSurjective hs).symm (ev P)) = ψpoly P
    rw [this]; rfl
  have hψx : ψA x = AdjoinRoot.of _ (LaurentPolynomial.T 1) := by
    simpa [hev, ψpoly] using hψA (MvPolynomial.X 0)
  have hψy : ψA y = AdjoinRoot.root _ := by
    simpa [hev, ψpoly] using hψA (MvPolynomial.X 1)
  have hψσ : ∀ k, ψA (σ k) = σM k := fun k => by
    simpa [hev, ψpoly] using hψA (MvPolynomial.C k)
  have hunit : IsUnit (ψA x) := by
    rw [hψx]
    exact (LaurentPolynomial.isUnit_T 1).map _
  let ψB : B →+* Mod K m := IsLocalization.Away.lift x (g := ψA) hunit
  have hψB : ∀ a, ψB (algebraMap A B a) = ψA a := fun a => IsLocalization.lift_eq _ _
  have hψΛ : ∀ c, ψB (Λ c) = AdjoinRoot.of _ c := by
    intro c
    have : ψB.comp Λ = AdjoinRoot.of _ := by
      refine laurent_hom_ext _ _ (fun k => ?_) ?_
      · simp only [RingHom.comp_apply, hΛC]
        show ψB (algebraMap A B (σ k)) = _
        rw [hψB, hψσ]; rfl
      · simp only [RingHom.comp_apply, hΛT]
        rw [hψB, hψx]
    exact congrArg (fun f => f c) this
  have hretr : ∀ z, ψB (Θ' z) = z := by
    intro z
    induction z using AdjoinRoot.induction_on with
    | ih p =>
      show ψB (Θ' (AdjoinRoot.mk _ p)) = AdjoinRoot.mk _ p
      rw [AdjoinRoot.lift_mk]
      induction p using Polynomial.induction_on' with
      | add p q hp hq => rw [Polynomial.eval₂_add, map_add, hp, hq, map_add]
      | monomial n c =>
        have e : (Polynomial.monomial n c : Polynomial (LaurentPolynomial K)) =
            Polynomial.C c * Polynomial.X ^ n := by rw [Polynomial.C_mul_X_pow_eq_monomial]
        rw [e, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, map_mul, map_pow,
          hψΛ, ← hΘ'root, hΘ'root, hψB, hψy, map_mul, map_pow, AdjoinRoot.mk_C,
          AdjoinRoot.mk_X]
  have hinj : Function.Injective Θ' := Function.LeftInverse.injective hretr
  have hmem : ∀ P : MvPolynomial (Fin 2) K, algebraMap A B (ev P) ∈ Θ'.range := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      refine ⟨AdjoinRoot.of _ (LaurentPolynomial.C a), ?_⟩
      rw [hΘ'of, hΛC]
      simp [σB, hev]
    | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, map_mul]
      obtain ⟨f, hf⟩ := hp
      fin_cases i
      · refine ⟨f * AdjoinRoot.of _ (LaurentPolynomial.T 1), ?_⟩
        rw [map_mul, hf, hΘ'of, hΛT]
        simp [hev]
      · refine ⟨f * AdjoinRoot.root _, ?_⟩
        rw [map_mul, hf, hΘ'root]
        simp [hev]
  have hsurj : Function.Surjective Θ' := by
    intro z
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers x) z
    obtain ⟨P, rfl⟩ := hs b
    have hz' : z * algebraMap A B (x ^ k) = algebraMap A B (ev P) := hz
    obtain ⟨f, hf⟩ := hmem P
    refine ⟨f * AdjoinRoot.of _ (LaurentPolynomial.T (-(k : ℤ))), ?_⟩
    rw [map_mul, hf, ← hz', mul_assoc]
    have h1 : Θ' (AdjoinRoot.of _ (LaurentPolynomial.T (-(k : ℤ)))) = ↑(hx.unit⁻¹ ^ k) := by
      rw [hΘ'of]
      exact LaurentPolynomial.eval₂_T_neg_n _ _ k
    rw [h1, map_pow]
    have hinv := Units.mul_inv hx.unit
    rw [IsUnit.unit_spec] at hinv
    rw [Units.val_pow_eq_pow_val, ← mul_pow, hinv, one_pow, mul_one]
  refine ⟨RingEquiv.ofBijective Θ' ⟨hinj, hsurj⟩, ?_, ?_, ?_⟩
  · exact (hΘ'of _).trans hΛT
  · exact hΘ'root
  · intro k
    exact (hΘ'of _).trans (hΛC k)

/-- The variable `y` of the model. -/
private noncomputable abbrev Yr (K : Type u) [Field K] (m : ℕ) : Mod K m := AdjoinRoot.root _

private theorem root_pow_succ (m : ℕ) : Yr K m ^ (m + 1) = 0 := by
  simpa using AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial (LaurentPolynomial K)) ^ (m + 1))

/-- The projection `K[x^±][y]/(y^(m+2)) → K[x^±][y]/(y^(m+1))`. -/
private noncomputable def proj (m : ℕ) : Mod K (m + 1) →+* Mod K m :=
  AdjoinRoot.lift (AdjoinRoot.of _) (Yr K m) (by
    have := root_pow_succ (K := K) m
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
    rw [pow_succ, this, zero_mul])

private theorem proj_of (m : ℕ) (c : LaurentPolynomial K) :
    proj m (AdjoinRoot.of _ c) = AdjoinRoot.of _ c := AdjoinRoot.lift_of _

private theorem proj_root (m : ℕ) : proj m (Yr K (m + 1)) = Yr K m :=
  AdjoinRoot.lift_root _

private theorem proj_mk (m : ℕ) (p : Polynomial (LaurentPolynomial K)) :
    proj m (AdjoinRoot.mk _ p) = AdjoinRoot.mk _ p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | monomial n c =>
    have e : (Polynomial.monomial n c : Polynomial (LaurentPolynomial K)) =
        Polynomial.C c * Polynomial.X ^ n := by rw [Polynomial.C_mul_X_pow_eq_monomial]
    simp only [e, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, proj_of, proj_root]

private theorem proj_surjective (m : ℕ) : Function.Surjective (proj (K := K) m) := by
  intro z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  exact ⟨AdjoinRoot.mk _ p, proj_mk m p⟩

private theorem proj_eq_zero_iff (m : ℕ) (p : Polynomial (LaurentPolynomial K)) :
    proj m (AdjoinRoot.mk _ p) = 0 ↔
      (Polynomial.X : Polynomial (LaurentPolynomial K)) ^ (m + 1) ∣ p := by
  rw [proj_mk, AdjoinRoot.mk_eq_zero]

private theorem mod_ker (m : ℕ) (z : Mod K (m + 1)) (hz : proj m z = 0) :
    ∃ c : LaurentPolynomial K, z = AdjoinRoot.of _ c * Yr K (m + 1) ^ (m + 1) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨q, rfl⟩ := (proj_eq_zero_iff m p).1 hz
  refine ⟨q.coeff 0, ?_⟩
  have hq : q = Polynomial.divX q * Polynomial.X + Polynomial.C (q.coeff 0) :=
    (Polynomial.divX_mul_X_add q).symm
  have h2 : Yr K (m + 1) ^ (m + 1 + 1) = 0 := root_pow_succ (m + 1)
  have hq' : (AdjoinRoot.mk _ q : Mod K (m + 1)) =
      AdjoinRoot.mk _ (Polynomial.divX q) * Yr K (m + 1) + AdjoinRoot.of _ (q.coeff 0) := by
    conv_lhs => rw [hq]
    rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  rw [map_mul, map_pow, AdjoinRoot.mk_X, hq']
  calc Yr K (m + 1) ^ (m + 1) *
        (AdjoinRoot.mk _ (Polynomial.divX q) * Yr K (m + 1) + AdjoinRoot.of _ (q.coeff 0))
      = AdjoinRoot.mk _ (Polynomial.divX q) * Yr K (m + 1) ^ (m + 1 + 1) +
        AdjoinRoot.of _ (q.coeff 0) * Yr K (m + 1) ^ (m + 1) := by ring
    _ = _ := by rw [h2, mul_zero, zero_add]

private theorem mod_ann (m : ℕ) (z : Mod K (m + 1)) (hz : z * Yr K (m + 1) = 0) : proj m z = 0 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  have hY : Yr K (m + 1) = AdjoinRoot.mk _ Polynomial.X := AdjoinRoot.mk_X.symm
  rw [hY, ← map_mul, AdjoinRoot.mk_eq_zero] at hz
  rw [proj_eq_zero_iff]
  obtain ⟨q, hq⟩ := hz
  refine ⟨q, ?_⟩
  have hX : (Polynomial.X : Polynomial (LaurentPolynomial K)) ≠ 0 := Polynomial.X_ne_zero
  apply mul_left_cancel₀ hX
  rw [← mul_assoc, ← pow_succ', mul_comm Polynomial.X p, hq]

private theorem isUnit_Tpow (m b : ℕ) :
    IsUnit ((AdjoinRoot.of ((Polynomial.X : Polynomial (LaurentPolynomial K)) ^ (m + 1))
      (LaurentPolynomial.T 1)) ^ b) :=
  ((LaurentPolynomial.isUnit_T 1).map (AdjoinRoot.of _)).pow b

private theorem ratio_exists_mod (b : ℕ) (ξ : ∀ m, Mod K m) (hξ : ∀ m, proj m (ξ (m + 1)) = ξ m)
    (hξ1 : ξ 1 = (AdjoinRoot.of _ (LaurentPolynomial.T 1)) ^ b * Yr K 1) :
    ∃ c : ∀ m, Mod K m, (∀ m, IsUnit (c m)) ∧
      (∀ m, ξ m = c m * ((AdjoinRoot.of _ (LaurentPolynomial.T 1)) ^ b * Yr K m)) ∧
      (∀ m, proj m (c (m + 1)) = c m) ∧ c 0 = 1 := by
  classical
  have hQ : ∀ k, ∃ w : Mod K (k + 1),
      ξ (k + 1) = (AdjoinRoot.of _ (LaurentPolynomial.T 1)) ^ b * Yr K (k + 1) +
        Yr K (k + 1) ^ 2 * w := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, ?_⟩
      rw [hξ1]; simp
    | succ k ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨w', hw'⟩ := proj_surjective (K := K) (k + 1) w
      have hz : proj (k + 1) (ξ (k + 1 + 1) - ((AdjoinRoot.of _ (LaurentPolynomial.T 1)) ^ b *
          Yr K (k + 1 + 1) + Yr K (k + 1 + 1) ^ 2 * w')) = 0 := by
        rw [map_sub, hξ, map_add, map_mul, map_mul, map_pow, map_pow, proj_of, proj_root, hw', hw]
        ring
      obtain ⟨c, hc⟩ := mod_ker (k + 1) _ hz
      refine ⟨w' + AdjoinRoot.of _ c * Yr K (k + 1 + 1) ^ k, ?_⟩
      have : ξ (k + 1 + 1) = (AdjoinRoot.of _ (LaurentPolynomial.T 1)) ^ b * Yr K (k + 1 + 1) +
          Yr K (k + 1 + 1) ^ 2 * w' + AdjoinRoot.of _ c * Yr K (k + 1 + 1) ^ (k + 1 + 1) := by
        rw [← hc]; ring
      rw [this]; ring
  choose w hw using hQ
  -- the ratio at level `k + 1`
  let cc : ∀ k, Mod K (k + 1) := fun k =>
    1 + (↑((isUnit_Tpow (K := K) (k + 1) b).unit⁻¹) : Mod K (k + 1)) * Yr K (k + 1) * w k
  have hcc_unit : ∀ k, IsUnit (cc k) := by
    intro k
    refine IsNilpotent.isUnit_one_add ⟨k + 2, ?_⟩
    have h0 : Yr K (k + 1) ^ (k + 2) = 0 := root_pow_succ (k + 1)
    rw [mul_pow, mul_pow, h0, mul_zero, zero_mul]
  have hcc : ∀ k, ξ (k + 1) = cc k * ((AdjoinRoot.of _ (LaurentPolynomial.T 1)) ^ b *
      Yr K (k + 1)) := by
    intro k
    have hu := Units.inv_mul (isUnit_Tpow (K := K) (k + 1) b).unit
    rw [IsUnit.unit_spec] at hu
    simp only [cc]
    rw [hw k]
    linear_combination (-(Yr K (k + 1) ^ 2 * w k)) * hu
  -- ratio at level `m`
  refine ⟨fun m => proj m (cc m), fun m => (hcc_unit m).map _, fun m => ?_, fun m => ?_, ?_⟩
  · -- `ξ m = proj (ξ (m+1))`
    show ξ m = proj m (cc m) * _
    rw [← hξ m, hcc m, map_mul, map_mul, map_pow, proj_of, proj_root]
  · -- compatibility
    show proj m (proj (m + 1) (cc (m + 1))) = proj m (cc m)
    have hd : (proj (m + 1) (cc (m + 1)) - cc m) * Yr K (m + 1) = 0 := by
      have e1 := hcc (m + 1)
      have e2 := hcc m
      have e3 : proj (m + 1) (ξ (m + 1 + 1)) = ξ (m + 1) := hξ (m + 1)
      rw [e1, map_mul, map_mul, map_pow, proj_of, proj_root] at e3
      rw [e2] at e3
      -- `(proj cc' - cc m) * (T^b * Y) = 0`
      have h4 : (proj (m + 1) (cc (m + 1)) - cc m) *
          ((AdjoinRoot.of _ (LaurentPolynomial.T 1)) ^ b * Yr K (m + 1)) = 0 := by
        rw [sub_mul, e3, sub_self]
      have hu := isUnit_Tpow (K := K) (m + 1) b
      have := (hu.mul_left_eq_zero (a := (proj (m + 1) (cc (m + 1)) - cc m) * Yr K (m + 1))).1
        (by rw [← h4]; ring)
      exact this
    have := mod_ann m _ hd
    rw [map_sub] at this
    exact sub_eq_zero.1 this
  · -- `c 0 = 1`
    show proj 0 (cc 0) = 1
    have e := hcc 0
    rw [hξ1] at e
    have h4 : (cc 0 - 1) * ((AdjoinRoot.of _ (LaurentPolynomial.T 1)) ^ b * Yr K 1) = 0 := by
      rw [sub_mul, ← e, one_mul, sub_self]
    have hu := isUnit_Tpow (K := K) 1 b
    have h5 : (cc 0 - 1) * Yr K 1 = 0 :=
      (hu.mul_left_eq_zero (a := (cc 0 - 1) * Yr K 1)).1 (by rw [← h4]; ring)
    have := mod_ann 0 _ h5
    rw [map_sub, map_one] at this
    exact sub_eq_zero.1 this

end

section

variable {K : Type u} [Field K]

/-- `T⁻¹`. -/
private noncomputable abbrev ti (K : Type u) [Field K] : LaurentPolynomial K :=
    LaurentPolynomial.T (-1)
/-- `T`. -/
private noncomputable abbrev tn (K : Type u) [Field K] : LaurentPolynomial K :=
    LaurentPolynomial.T 1

private theorem tn_mul_ti : tn K * ti K = 1 := by
  simp only [tn, ti]; rw [← T_add]; simp

/-- Evaluation of a polynomial at `T⁻¹`. -/
private noncomputable def invEval (q : Polynomial K) : LaurentPolynomial K :=
  Polynomial.eval₂ LaurentPolynomial.C (ti K) q

private theorem invEval_add (p q : Polynomial K) : invEval (p + q) = invEval p + invEval q :=
  Polynomial.eval₂_add _ _

private theorem invEval_mul (p q : Polynomial K) : invEval (p * q) = invEval p * invEval q :=
  Polynomial.eval₂_mul _ _

private theorem invEval_X_pow (k : ℕ) : invEval (Polynomial.X ^ k : Polynomial K) = ti K ^ k := by
  simp [invEval]

private theorem invEval_C (a : K) : invEval (Polynomial.C a) = LaurentPolynomial.C a := by
  simp [invEval]

private theorem invEval_neg (q : Polynomial K) : invEval (-q) = -invEval q := by
  simp [invEval, Polynomial.eval₂_neg]

private theorem toLaurent_X_pow (k : ℕ) : Polynomial.toLaurent (Polynomial.X ^ k : Polynomial K) =
    tn K ^ k := by
  simp [tn, T_pow]

/-- Every Laurent polynomial is a polynomial in `T` plus `T⁻¹` times a polynomial in `T⁻¹`. -/
private theorem laurent_split (h : LaurentPolynomial K) :
    ∃ p q : Polynomial K, h = Polynomial.toLaurent p + ti K * invEval q := by
  refine LaurentPolynomial.induction_on' h ?_ ?_
  · rintro p q ⟨p1, q1, h1⟩ ⟨p2, q2, h2⟩
    exact ⟨p1 + p2, q1 + q2, by rw [h1, h2, map_add, invEval_add]; ring⟩
  · intro n a
    rcases le_or_gt 0 n with hn | hn
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      refine ⟨Polynomial.C a * Polynomial.X ^ k, 0, ?_⟩
      have h0 : invEval (0 : Polynomial K) = 0 := by simp [invEval]
      simp [h0]
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
      refine ⟨0, Polynomial.C a * Polynomial.X ^ k, ?_⟩
      rw [hk, invEval_mul, invEval_C, invEval_X_pow]
      simp only [ti, map_zero, zero_add]
      have e : (LaurentPolynomial.T (-1) : LaurentPolynomial K) ^ k =
          LaurentPolynomial.T (-(k : ℤ)) := by rw [T_pow]; congr 1; ring
      rw [e, mul_left_comm, ← T_add]
      congr 2
      ring

/-- The image in the overlap of the chart `j` correction `p` (`L`-side), as a coefficient of
`y^d`: `T^d p(T)` for `j ≥ 1` and `p(T)` for `j = 0`. -/
private noncomputable def Lx (d j : ℕ) (p : Polynomial K) : LaurentPolynomial K :=
  if j = 0 then Polynomial.toLaurent p else tn K ^ d * Polynomial.toLaurent p

/-- The image in the overlap `k - 1` of the chart `k` correction (`R`-side). -/
private noncomputable def Rx (d r b k : ℕ) (p q : Polynomial K) : LaurentPolynomial K :=
  if k = r then tn K ^ (b * d) * invEval q
  else tn K ^ ((b - 1) * d) * (LaurentPolynomial.C (p.coeff 0) + ti K * invEval q)

private theorem tn_pow_mul_ti_pow (k : ℕ) : tn K ^ k * ti K ^ k = 1 := by
  rw [← mul_pow, tn_mul_ti, one_pow]

private theorem Lx_lift (d m : ℕ) (pa : Polynomial K) :
    Lx d m (if m = 0 then Polynomial.X ^ d * pa else pa) = tn K ^ d * Polynomial.toLaurent pa := by
  by_cases hm : m = 0
  · simp [Lx, hm, toLaurent_X_pow]
  · simp [Lx, hm]

/-- Choosing the `R`-side correction of the last chart so that the low part cancels. -/
private theorem admissible_last (d b : ℕ) (hb : 2 ≤ b) (g : LaurentPolynomial K) (r : ℕ) :
    ∃ q pa : Polynomial K, g + Rx d r b r 0 q = tn K ^ d * Polynomial.toLaurent pa := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
  obtain ⟨pδ, qδ, h⟩ := laurent_split (g * ti K ^ d)
  have h1 := tn_pow_mul_ti_pow (K := K) d
  have hg : g = tn K ^ d * (Polynomial.toLaurent pδ + ti K * invEval qδ) := by
    rw [← h]; linear_combination (-g) * h1
  refine ⟨-(Polynomial.X ^ ((c + 1) * d + 1) * qδ), pδ, ?_⟩
  have w1 := tn_pow_mul_ti_pow (K := K) ((c + 1) * d)
  have e1 : tn K ^ ((c + 2) * d) = tn K ^ d * tn K ^ ((c + 1) * d) := by
    rw [← pow_add]; congr 1; ring
  simp only [Rx, ite_true, invEval_neg, invEval_mul, invEval_X_pow, e1]
  rw [hg, pow_succ (ti K) ((c + 1) * d)]
  linear_combination (-(tn K ^ d * ti K * invEval qδ)) * w1

/-- Choosing the `R`-side correction of an interior chart so that the low part cancels. -/
private theorem admissible_mid (d b : ℕ) (hb : 2 ≤ b) (g : LaurentPolynomial K) (r k : ℕ)
    (hk : k ≠ r)
    (p : Polynomial K) :
    ∃ q pa : Polynomial K, g + Rx d r b k p q = tn K ^ d * Polynomial.toLaurent pa := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
  obtain ⟨pδ, qδ, h⟩ := laurent_split (g * ti K ^ d)
  have h1 := tn_pow_mul_ti_pow (K := K) d
  have hg : g = tn K ^ d * (Polynomial.toLaurent pδ + ti K * invEval qδ) := by
    rw [← h]; linear_combination (-g) * h1
  refine ⟨-(Polynomial.X ^ (c * d) * qδ),
    pδ + Polynomial.C (p.coeff 0) * Polynomial.X ^ (c * d), ?_⟩
  have w0 := tn_pow_mul_ti_pow (K := K) (c * d)
  have e1 : tn K ^ ((c + 2 - 1) * d) = tn K ^ d * tn K ^ (c * d) := by
    rw [← pow_add]; congr 1
    have : c + 2 - 1 = c + 1 := by omega
    rw [this]; ring
  simp only [Rx, hk, ite_false, invEval_neg, invEval_mul, invEval_X_pow, e1, map_add, map_mul,
    Polynomial.toLaurent_C, toLaurent_X_pow]
  rw [hg]
  linear_combination (-(tn K ^ d * ti K * invEval qδ)) * w0

/-- The equations of the overlap `j`. -/
private def EqAt (d r : ℕ) (bb : ℕ → ℕ) (e δ : ℕ → LaurentPolynomial K)
    (pα pβ qα qβ : ℕ → Polynomial K) (j : ℕ) : Prop :=
  e j + Rx d r (bb j) (j + 1) (pα (j + 1)) (qα (j + 1)) - (bb j : LaurentPolynomial K) * Lx d j
      (pα j) -
      Lx d j (pβ j) = 0 ∧
    δ j + Rx d r (bb j) (j + 1) (pβ (j + 1)) (qβ (j + 1)) + Lx d j (pα j) = 0

/-- The `R`-side of the chart `m + 1` makes the `L`-side of the chart `m` admissible. -/
private def AdmAt (d r : ℕ) (bb : ℕ → ℕ) (e δ : ℕ → LaurentPolynomial K)
    (pα pβ qα qβ : ℕ → Polynomial K) (m : ℕ) : Prop :=
  (∃ pa : Polynomial K, δ m + Rx d r (bb m) (m + 1) (pβ (m + 1)) (qβ (m + 1)) =
      tn K ^ d * Polynomial.toLaurent pa) ∧
    ∃ pb : Polynomial K, (e m + (bb m : LaurentPolynomial K) * δ m +
      (bb m : LaurentPolynomial K) * Rx d r (bb m) (m + 1) (pβ (m + 1)) (qβ (m + 1))) +
      Rx d r (bb m) (m + 1) (pα (m + 1)) (qα (m + 1)) = tn K ^ d * Polynomial.toLaurent pb

private theorem chain_laurent (d r : ℕ) (hr : 0 < r) (bb : ℕ → ℕ) (hb : ∀ j, 2 ≤ bb j)
    (e δ : ℕ → LaurentPolynomial K) :
    ∃ pα pβ qα qβ : ℕ → Polynomial K, ∀ j, j < r → EqAt d r bb e δ pα pβ qα qβ j := by
  have key : ∀ t, t ≤ r → ∃ pα pβ qα qβ : ℕ → Polynomial K,
      (∀ j, r - t ≤ j → j < r → EqAt d r bb e δ pα pβ qα qβ j) ∧
      (1 ≤ r - t → AdmAt d r bb e δ pα pβ qα qβ (r - t - 1)) := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨qb, pa, hqb⟩ := admissible_last d (bb (r - 1)) (hb _) (δ (r - 1)) r
      obtain ⟨qa, pb, hqa⟩ := admissible_last d (bb (r - 1)) (hb _)
        (e (r - 1) + (bb (r - 1) : LaurentPolynomial K) * δ (r - 1) +
          (bb (r - 1) : LaurentPolynomial K) * Rx d r (bb (r - 1)) r (0 : Polynomial K) qb) r
      refine ⟨fun _ => 0, fun _ => 0, fun i => if i = r then qa else 0,
        fun i => if i = r then qb else 0, fun j hj1 hj2 => absurd hj2 (by omega), fun _ => ?_⟩
      have hm : r - 0 - 1 + 1 = r := by omega
      refine ⟨⟨pa, ?_⟩, ⟨pb, ?_⟩⟩
      · simp only [hm, if_true]
        exact hqb
      · simp only [hm, if_true]
        exact hqa
    | succ t ih =>
      intro ht
      obtain ⟨pα, pβ, qα, qβ, hEq, hAdm⟩ := ih (by omega)
      have hm1 : 1 ≤ r - t := by omega
      obtain ⟨⟨pa, hpa⟩, ⟨pb, hpb⟩⟩ := hAdm hm1
      obtain ⟨m, hm⟩ : ∃ m, r - t = m + 1 := ⟨r - t - 1, by omega⟩
      have hm' : r - (t + 1) = m := by omega
      have hmr : m < r := by omega
      have hAdmm : r - t - 1 = m := by omega
      rw [hAdmm] at hpa hpb
      let lift : Polynomial K → Polynomial K := fun p => if m = 0 then Polynomial.X ^ d * p else p
      let pα1 : ℕ → Polynomial K := Function.update pα m (-(lift pa))
      let pβ1 : ℕ → Polynomial K := Function.update pβ m (lift pb)
      have hLα : Lx d m (pα1 m) = -(tn K ^ d * Polynomial.toLaurent pa) := by
        simp only [pα1, Function.update_self]
        have := Lx_lift (K := K) d m pa
        have hneg : ∀ p : Polynomial K, Lx d m (-p) = -Lx d m p := by
          intro p; by_cases h0 : m = 0 <;> simp [Lx, h0]
        simp only [lift]
        rw [hneg, this]
      have hLβ : Lx d m (pβ1 m) = tn K ^ d * Polynomial.toLaurent pb := by
        simp only [pβ1, Function.update_self]
        exact Lx_lift (K := K) d m pb
      have hE1 : EqAt d r bb e δ pα1 pβ1 qα qβ m := by
        have h1 : pα1 (m + 1) = pα (m + 1) := Function.update_of_ne (by omega) _ _
        have h2 : pβ1 (m + 1) = pβ (m + 1) := Function.update_of_ne (by omega) _ _
        unfold EqAt
        rw [h1, h2, hLα, hLβ]
        refine ⟨?_, ?_⟩
        · linear_combination (-(bb m : LaurentPolynomial K)) * hpa + hpb
        · linear_combination hpa
      have hEj : ∀ j, r - t ≤ j → j < r → EqAt d r bb e δ pα1 pβ1 qα qβ j := by
        intro j hj1 hj2
        have e1 : pα1 j = pα j := Function.update_of_ne (by omega) _ _
        have e2 : pβ1 j = pβ j := Function.update_of_ne (by omega) _ _
        have e3 : pα1 (j + 1) = pα (j + 1) := Function.update_of_ne (by omega) _ _
        have e4 : pβ1 (j + 1) = pβ (j + 1) := Function.update_of_ne (by omega) _ _
        unfold EqAt
        rw [e1, e2, e3, e4]
        exact hEq j hj1 hj2
      have hAll : ∀ j, m ≤ j → j < r → EqAt d r bb e δ pα1 pβ1 qα qβ j := by
        intro j hj1 hj2
        rcases Nat.eq_or_lt_of_le hj1 with h | h
        · rw [← h]; exact hE1
        · exact hEj j (by omega) hj2
      rw [hm']
      rcases m with _ | m'
      · exact ⟨pα1, pβ1, qα, qβ, fun j hj1 hj2 => hAll j hj1 hj2,
          fun h => absurd h (by omega)⟩
      · obtain ⟨qb', pa', hqb⟩ := admissible_mid d (bb m') (hb _) (δ m') r (m' + 1) (by omega)
          (pβ1 (m' + 1))
        obtain ⟨qa', pb', hqa⟩ := admissible_mid d (bb m') (hb _)
          (e m' + (bb m' : LaurentPolynomial K) * δ m' +
            (bb m' : LaurentPolynomial K) * Rx d r (bb m') (m' + 1) (pβ1 (m' + 1)) qb') r (m' + 1)
          (by omega) (pα1 (m' + 1))
        refine ⟨pα1, pβ1, Function.update qα (m' + 1) qa', Function.update qβ (m' + 1) qb', ?_, ?_⟩
        · intro j hj1 hj2
          have h0 := hAll j hj1 hj2
          have e1 : Function.update qα (m' + 1) qa' (j + 1) = qα (j + 1) :=
            Function.update_of_ne (by omega) _ _
          have e2 : Function.update qβ (m' + 1) qb' (j + 1) = qβ (j + 1) :=
            Function.update_of_ne (by omega) _ _
          unfold EqAt
          rw [e1, e2]
          exact h0
        · intro _
          show AdmAt d r bb e δ pα1 pβ1 (Function.update qα (m' + 1) qa')
            (Function.update qβ (m' + 1) qb') (m' + 1 - 1)
          have : m' + 1 - 1 = m' := by omega
          rw [this]
          unfold AdmAt
          simp only [Function.update_self]
          exact ⟨⟨pa', hqb⟩, ⟨pb', hqa⟩⟩
  obtain ⟨pα, pβ, qα, qβ, hEq, -⟩ := key r le_rfl
  exact ⟨pα, pβ, qα, qβ, fun j hj => hEq j (by omega) hj⟩

end

section Eval

variable {K : Type u} [Field K]

/-- The constants `K → Mod K m`. -/
private noncomputable def σMod (K : Type u) [Field K] (m : ℕ) : K →+* Mod K m :=
  (AdjoinRoot.of _).comp (LaurentPolynomial.C : K →+* LaurentPolynomial K)

/-- `z ≡ z'` modulo `y`. -/
private def cgY (m : ℕ) (z z' : Mod K m) : Prop := ∃ w, z = z' + Yr K m * w

private theorem cgY_refl (m : ℕ) (z : Mod K m) : cgY m z z := ⟨0, by ring⟩

private theorem cgY_add {m : ℕ} {z z' u u' : Mod K m} (h1 : cgY m z z') (h2 : cgY m u u') :
    cgY m (z + u) (z' + u') := by
  obtain ⟨w1, h1⟩ := h1; obtain ⟨w2, h2⟩ := h2
  exact ⟨w1 + w2, by rw [h1, h2]; ring⟩

private theorem cgY_mul {m : ℕ} {z z' u u' : Mod K m} (h1 : cgY m z z') (h2 : cgY m u u') :
    cgY m (z * u) (z' * u') := by
  obtain ⟨w1, h1⟩ := h1; obtain ⟨w2, h2⟩ := h2
  exact ⟨w1 * u' + z' * w2 + Yr K m * w1 * w2, by rw [h1, h2]; ring⟩

private theorem cgY_pow {m : ℕ} {z z' : Mod K m} (h : cgY m z z') (n : ℕ) :
    cgY m (z ^ n) (z' ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact cgY_refl m 1
  | succ n ih => have := cgY_mul ih h; rwa [← pow_succ, ← pow_succ] at this

private theorem cgY_mul_Ypow {m : ℕ} {z z' : Mod K m} (h : cgY m z z') :
    z * Yr K m ^ m = z' * Yr K m ^ m := by
  obtain ⟨w, h⟩ := h
  have h0 : Yr K m ^ (m + 1) = 0 := root_pow_succ m
  rw [h]; linear_combination w * h0

private theorem poly_cg {m : ℕ} (σ : K →+* Mod K m) {a b : Mod K m} (h : cgY m a b)
    (p : Polynomial K) : cgY m (p.eval₂ σ a) (p.eval₂ σ b) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨z, hz⟩ := Polynomial.sub_dvd_eval_sub a b (p.map σ)
  rw [Polynomial.eval_map, Polynomial.eval_map] at hz
  refine ⟨w * z, ?_⟩
  have : a - b = Yr K m * w := by rw [hw]; ring
  rw [this] at hz
  linear_combination hz

private theorem poly_eval_zero {m : ℕ} (σ : K →+* Mod K m) {a : Mod K m} (h : cgY m a 0)
    (p : Polynomial K) : cgY m (p.eval₂ σ a) (σ (p.coeff 0)) := by
  have := poly_cg σ h p
  simpa [Polynomial.eval₂_at_zero] using this

/-- The polynomial in `K[X₀, X₁]` of the correction of the chart `k` with data `p`, `q`. -/
private noncomputable def fpoly (r m k : ℕ) (p q : Polynomial K) : MvPolynomial (Fin 2) K :=
  if k = 0 then MvPolynomial.X 1 ^ m * Polynomial.aeval (MvPolynomial.X 0) p
  else if k = r then MvPolynomial.X 0 ^ m * Polynomial.aeval (MvPolynomial.X 1) q
  else (MvPolynomial.X 0 * MvPolynomial.X 1) ^ m *
    (Polynomial.aeval (MvPolynomial.X 0) p +
      MvPolynomial.X 1 * Polynomial.aeval (MvPolynomial.X 1) q)

private theorem ev_aeval {S : Type*} [CommRing S] (σ : K →+* S) (u v : S) (i : Fin 2)
    (p : Polynomial K) :
    MvPolynomial.eval₂Hom σ ![u, v] (Polynomial.aeval (MvPolynomial.X i) p) =
      p.eval₂ σ (![u, v] i) := by
  have h1 : (MvPolynomial.eval₂Hom σ ![u, v]).comp (algebraMap K (MvPolynomial (Fin 2) K)) = σ := by
    ext a; simp
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, h1, MvPolynomial.eval₂Hom_X']

private theorem ofL_toLaurent (m : ℕ) (p : Polynomial K) :
    (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K m) (Polynomial.toLaurent p) =
      p.eval₂ (σMod K m) (AdjoinRoot.of _ (tn K)) := by
  have : ((AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K m).comp
      (Polynomial.toLaurent : Polynomial K →+* LaurentPolynomial K)) =
      Polynomial.eval₂RingHom (σMod K m) (AdjoinRoot.of _ (tn K)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [σMod]
    · simp [tn]
  exact congrArg (fun f => f p) this

private theorem ofL_invEval (m : ℕ) (q : Polynomial K) :
    (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K m) (invEval q) =
      q.eval₂ (σMod K m) (AdjoinRoot.of _ (ti K)) := by
  rw [invEval, Polynomial.hom_eval₂]
  rfl

private theorem ofL_tn_mul_ti (m : ℕ) :
    (AdjoinRoot.of _ (tn K) : Mod K m) * AdjoinRoot.of _ (ti K) = 1 := by
  rw [← map_mul, tn_mul_ti, map_one]

private theorem evalL_fpoly (m r k : ℕ) (hk : k ≠ r) (p q : Polynomial K) :
    MvPolynomial.eval₂Hom (σMod K m) ![AdjoinRoot.of _ (tn K), Yr K m] (fpoly r m k p q) =
      (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K m) (Lx m k p) * Yr K m ^ m := by
  by_cases h0 : k = 0
  · subst h0
    simp only [fpoly, Lx, if_true, map_mul, map_pow, MvPolynomial.eval₂Hom_X', ev_aeval,
      ofL_toLaurent]
    simp
    ring
  · simp only [fpoly, Lx, h0, hk, ite_false, map_mul, map_pow, map_add, MvPolynomial.eval₂Hom_X',
      ev_aeval, ofL_toLaurent]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hcg : cgY m ((AdjoinRoot.of _ (tn K) : Mod K m) ^ m *
        (p.eval₂ (σMod K m) (AdjoinRoot.of _ (tn K)) +
          Yr K m * q.eval₂ (σMod K m) (Yr K m)))
        ((AdjoinRoot.of _ (tn K) : Mod K m) ^ m * p.eval₂ (σMod K m) (AdjoinRoot.of _ (tn K))) :=
      ⟨(AdjoinRoot.of _ (tn K) : Mod K m) ^ m * q.eval₂ (σMod K m) (Yr K m), by ring⟩
    have := cgY_mul_Ypow hcg
    calc _ = ((AdjoinRoot.of _ (tn K) : Mod K m) ^ m *
        (p.eval₂ (σMod K m) (AdjoinRoot.of _ (tn K)) +
          Yr K m * q.eval₂ (σMod K m) (Yr K m))) * Yr K m ^ m := by ring
      _ = _ := this

private theorem evalR_fpoly (m r b k : ℕ) (hb : 1 ≤ b) (hk : k ≠ 0) (c s : Mod K m)
    (hc : cgY m c 1) (hs : cgY m s 1) (p q : Polynomial K) :
    MvPolynomial.eval₂Hom (σMod K m)
      ![c * (AdjoinRoot.of _ (tn K)) ^ b * Yr K m, s * AdjoinRoot.of _ (ti K)] (fpoly r m k p q) =
      (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K m) (Rx m r b k p q) * Yr K m ^ m := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  set T : Mod K m := AdjoinRoot.of _ (tn K) with hT
  set Ti : Mod K m := AdjoinRoot.of _ (ti K) with hTi
  have hTT : T * Ti = 1 := ofL_tn_mul_ti m
  have hsTi : cgY m (s * Ti) Ti := by
    have := cgY_mul hs (cgY_refl m Ti); simpa using this
  have hξ : cgY m (c * T ^ (b' + 1) * Yr K m) 0 := ⟨c * T ^ (b' + 1), by ring⟩
  have hTb : (T ^ (b' + 1) * Ti) = T ^ b' := by
    linear_combination T ^ b' * hTT
  by_cases hkr : k = r
  · subst hkr
    simp only [fpoly, Rx, hk, ite_true, ite_false, map_mul, map_pow, MvPolynomial.eval₂Hom_X',
      ev_aeval, ofL_invEval]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hcg : cgY m (c ^ m * (T ^ (b' + 1)) ^ m * q.eval₂ (σMod K m) (s * Ti))
        (1 ^ m * (T ^ (b' + 1)) ^ m * q.eval₂ (σMod K m) Ti) :=
      cgY_mul (cgY_mul (cgY_pow hc m) (cgY_refl m _)) (poly_cg _ hsTi q)
    have := cgY_mul_Ypow hcg
    calc _ = (c ^ m * (T ^ (b' + 1)) ^ m * q.eval₂ (σMod K m) (s * Ti)) * Yr K m ^ m := by ring
      _ = _ := this.trans (by rw [← pow_mul]; ring)
  · simp only [fpoly, Rx, hk, hkr, ite_false, map_mul, map_pow, map_add, MvPolynomial.eval₂Hom_X',
      ev_aeval, ofL_invEval, Polynomial.toLaurent_C, Polynomial.eval₂_C]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have e0 : b' + 1 - 1 = b' := by omega
    rw [e0]
    have hbase : cgY m ((c * T ^ (b' + 1) * (s * Ti)) ^ m) ((T ^ b') ^ m) := by
      have h1 := cgY_pow (cgY_mul (cgY_mul hc (cgY_refl m (T ^ (b' + 1)))) (cgY_mul hs (cgY_refl m
          Ti))) m
      have e1 : (1 * T ^ (b' + 1) * (1 * Ti)) = T ^ b' := by rw [one_mul, one_mul]; exact hTb
      rwa [e1] at h1
    have hp := poly_eval_zero (σMod K m) hξ p
    have hq : cgY m (s * Ti * q.eval₂ (σMod K m) (s * Ti)) (Ti * q.eval₂ (σMod K m) Ti) :=
      cgY_mul hsTi (poly_cg _ hsTi q)
    have hcg := cgY_mul hbase (cgY_add hp hq)
    have := cgY_mul_Ypow hcg
    calc _ = ((c * T ^ (b' + 1) * (s * Ti)) ^ m * (p.eval₂ (σMod K m) (c * T ^ (b' + 1) * Yr K m) +
        s * Ti * q.eval₂ (σMod K m) (s * Ti))) * Yr K m ^ m := by ring
      _ = _ := this.trans (by rw [← pow_mul]; rfl)

/-- The exceptional ideal of the chart `k`, indexed by naturals. -/
private noncomputable def Jcn (K : Type u) [Field K] (r k : ℕ) : Ideal (MvPolynomial (Fin 2) K) :=
  if k = 0 then Ideal.span {MvPolynomial.X 1}
  else if k = r then Ideal.span {MvPolynomial.X 0}
  else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}

private theorem fpoly_mem (r m k : ℕ) (p q : Polynomial K) : fpoly r m k p q ∈ Jcn K r k ^ m := by
  by_cases h0 : k = 0
  · rw [fpoly, if_pos h0, Jcn, if_pos h0]
    exact Ideal.mul_mem_right _ _
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (MvPolynomial.X 1)) m)
  · by_cases hr : k = r
    · rw [fpoly, if_neg h0, if_pos hr, Jcn, if_neg h0, if_pos hr]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (MvPolynomial.X 0)) m)
    · rw [fpoly, if_neg h0, if_neg hr, Jcn, if_neg h0, if_neg hr]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self
          (MvPolynomial.X 0 * MvPolynomial.X 1)) m)

private theorem chain_mod (m : ℕ) (r : ℕ) (hr : 0 < r) (bb : ℕ → ℕ) (hb : ∀ j, 2 ≤ bb j)
    (cc ss : ℕ → Mod K m) (hc : ∀ j, cgY m (cc j) 1) (hs : ∀ j, cgY m (ss j) 1)
    (e δ : ℕ → LaurentPolynomial K) :
    ∃ pα pβ qα qβ : ℕ → Polynomial K, ∀ j, j < r →
        (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K m) (e j) * Yr K m ^ m +
          MvPolynomial.eval₂Hom (σMod K m)
            ![cc j * (AdjoinRoot.of _ (tn K)) ^ (bb j) * Yr K m, ss j * AdjoinRoot.of _ (ti K)]
            (fpoly r m (j + 1) (pα (j + 1)) (qα (j + 1))) -
          (bb j : Mod K m) * MvPolynomial.eval₂Hom (σMod K m)
            ![AdjoinRoot.of _ (tn K), Yr K m] (fpoly r m j (pα j) (qα j)) -
          MvPolynomial.eval₂Hom (σMod K m) ![AdjoinRoot.of _ (tn K), Yr K m]
            (fpoly r m j (pβ j) (qβ j)) = 0 ∧
        (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K m) (δ j) * Yr K m ^ m +
          MvPolynomial.eval₂Hom (σMod K m)
            ![cc j * (AdjoinRoot.of _ (tn K)) ^ (bb j) * Yr K m, ss j * AdjoinRoot.of _ (ti K)]
            (fpoly r m (j + 1) (pβ (j + 1)) (qβ (j + 1))) +
          MvPolynomial.eval₂Hom (σMod K m) ![AdjoinRoot.of _ (tn K), Yr K m]
            (fpoly r m j (pα j) (qα j)) = 0 := by
  obtain ⟨pα, pβ, qα, qβ, hE⟩ := chain_laurent m r hr bb hb e δ
  refine ⟨pα, pβ, qα, qβ, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := hE j hj
  have hjr : j ≠ r := by omega
  have hj1 : j + 1 ≠ 0 := by omega
  simp only [evalL_fpoly m r j hjr, evalR_fpoly m r (bb j) (j + 1) (by have := hb j; omega) hj1
    (cc j) (ss j) (hc j) (hs j)]
  refine ⟨?_, ?_⟩
  · have := congrArg (fun z => (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K m) z * Yr K m ^ m)
      h1
    simp only [map_sub, map_add, map_mul, map_zero, zero_mul, map_natCast] at this
    linear_combination this
  · have := congrArg (fun z => (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K m) z * Yr K m ^ m)
      h2
    simp only [map_sub, map_add, map_mul, map_zero, zero_mul, map_natCast] at this
    linear_combination this

/-- Evaluation of a polynomial at the left chart coordinates `(T, y)`. -/
private noncomputable def evL (m : ℕ) : MvPolynomial (Fin 2) K →+* Mod K m :=
  MvPolynomial.eval₂Hom (σMod K m) ![AdjoinRoot.of _ (tn K), Yr K m]

/-- Evaluation of a polynomial at the right chart coordinates `(c T^b y, s T⁻¹)`. -/
private noncomputable def evR (m : ℕ) (c s : Mod K m) (b : ℕ) :
    MvPolynomial (Fin 2) K →+* Mod K m :=
  MvPolynomial.eval₂Hom (σMod K m)
    ![c * (AdjoinRoot.of _ (tn K)) ^ b * Yr K m, s * AdjoinRoot.of _ (ti K)]

private theorem one_add_pow_sq {R : Type*} [CommRing R] (a : R) (h : a * a = 0) (b : ℕ) :
    (1 + a) ^ b = 1 + (b : R) * a := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ, ih]; push_cast; linear_combination (b : R) * h

private theorem solve_M (n : ℕ) (r : ℕ) (hr : 0 < r) (bb : ℕ → ℕ) (hb : ∀ j, 2 ≤ bb j)
    (cc ss uR uL vL vR : ℕ → Mod K (n + 1))
    (hc : ∀ j, cgY (n + 1) (cc j) 1) (hs : ∀ j, cgY (n + 1) (ss j) 1)
    (huL : ∀ j, cgY (n + 1) (uL j) 1) (hvL : ∀ j, cgY (n + 1) (vL j) 1)
    (hE1 : ∀ j, j < r → proj n (uR j * cc j) = proj n (uL j ^ bb j * vL j))
    (hE2 : ∀ j, j < r → proj n (ss j * vR j * uL j) = 1) :
    ∃ pα pβ qα qβ : ℕ → Polynomial K, ∀ j, j < r →
      uR j * (1 + evR (n + 1) (cc j) (ss j) (bb j)
          (fpoly r (n + 1) (j + 1) (pα (j + 1)) (qα (j + 1)))) * cc j =
        (uL j * (1 + evL (n + 1) (fpoly r (n + 1) j (pα j) (qα j)))) ^ bb j *
          (vL j * (1 + evL (n + 1) (fpoly r (n + 1) j (pβ j) (qβ j)))) ∧
      ss j * (vR j * (1 + evR (n + 1) (cc j) (ss j) (bb j)
          (fpoly r (n + 1) (j + 1) (pβ (j + 1)) (qβ (j + 1))))) *
        (uL j * (1 + evL (n + 1) (fpoly r (n + 1) j (pα j) (qα j)))) = 1 := by
  have hex : ∀ j, ∃ e0 d0 : LaurentPolynomial K, j < r →
      (uR j * cc j - uL j ^ bb j * vL j =
        (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K (n + 1)) e0 * Yr K (n + 1) ^ (n + 1)) ∧
      (ss j * vR j * uL j - 1 =
        (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K (n + 1)) d0 * Yr K (n + 1) ^ (n + 1)) := by
    intro j
    by_cases hj : j < r
    · obtain ⟨e0, h1⟩ := mod_ker n (uR j * cc j - uL j ^ bb j * vL j)
        (by rw [map_sub, hE1 j hj, sub_self])
      obtain ⟨d0, h2⟩ := mod_ker n (ss j * vR j * uL j - 1)
        (by rw [map_sub, hE2 j hj, map_one, sub_self])
      exact ⟨e0, d0, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose e0 d0 hed using hex
  obtain ⟨pα, pβ, qα, qβ, hch⟩ := chain_mod (n + 1) r hr bb hb cc ss hc hs e0 d0
  refine ⟨pα, pβ, qα, qβ, fun j hj => ?_⟩
  obtain ⟨hA, hD⟩ := hed j hj
  obtain ⟨c1, c2⟩ := hch j hj
  have hjr : j ≠ r := by omega
  have hj1 : j + 1 ≠ 0 := by omega
  have hbj : 1 ≤ bb j := by have := hb j; omega
  have hLα := evalL_fpoly (K := K) (n + 1) r j hjr (pα j) (qα j)
  have hLβ := evalL_fpoly (K := K) (n + 1) r j hjr (pβ j) (qβ j)
  have hRα := evalR_fpoly (K := K) (n + 1) r (bb j) (j + 1) hbj hj1 (cc j) (ss j) (hc j) (hs j)
    (pα (j + 1)) (qα (j + 1))
  have hRβ := evalR_fpoly (K := K) (n + 1) r (bb j) (j + 1) hbj hj1 (cc j) (ss j) (hc j) (hs j)
    (pβ (j + 1)) (qβ (j + 1))
  change evL (n + 1) _ = _ at hLα hLβ
  change evR (n + 1) _ _ _ _ = _ at hRα hRβ
  change _ + evR (n + 1) _ _ _ _ - _ * evL (n + 1) _ - evL (n + 1) _ = 0 at c1
  change _ + evR (n + 1) _ _ _ _ + evL (n + 1) _ = 0 at c2
  generalize evL (n + 1) (fpoly r (n + 1) j (pα j) (qα j)) = a at *
  generalize evL (n + 1) (fpoly r (n + 1) j (pβ j) (qβ j)) = bβ at *
  generalize evR (n + 1) (cc j) (ss j) (bb j) (fpoly r (n + 1) (j + 1) (pα (j + 1)) (qα (j + 1)))
      = a' at *
  generalize evR (n + 1) (cc j) (ss j) (bb j) (fpoly r (n + 1) (j + 1) (pβ (j + 1)) (qβ (j + 1)))
      = b' at *
  have hW : Yr K (n + 1) ^ (n + 1) * Yr K (n + 1) ^ (n + 1) = 0 := by
    rw [← pow_add]; exact pow_eq_zero_of_le (by omega) (root_pow_succ (n + 1))
  have hBq : (uL j ^ bb j * vL j) * Yr K (n + 1) ^ (n + 1) = Yr K (n + 1) ^ (n + 1) := by
    simpa using cgY_mul_Ypow (cgY_mul (cgY_pow (huL j) (bb j)) (hvL j))
  obtain ⟨A, hA_⟩ : ∃ A, a = A * Yr K (n + 1) ^ (n + 1) := ⟨_, hLα⟩
  obtain ⟨B, hB_⟩ : ∃ B, bβ = B * Yr K (n + 1) ^ (n + 1) := ⟨_, hLβ⟩
  obtain ⟨A', hA'_⟩ : ∃ A', a' = A' * Yr K (n + 1) ^ (n + 1) := ⟨_, hRα⟩
  obtain ⟨B', hB'_⟩ : ∃ B', b' = B' * Yr K (n + 1) ^ (n + 1) := ⟨_, hRβ⟩
  subst hA_ hB_ hA'_ hB'_
  set W := Yr K (n + 1) ^ (n + 1) with hWdef
  set eL := (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K (n + 1)) (e0 j) with heL
  set dL := (AdjoinRoot.of _ : LaurentPolynomial K →+* Mod K (n + 1)) (d0 j) with hdL
  refine ⟨?_, ?_⟩
  · rw [mul_pow, one_add_pow_sq (A * W) (by linear_combination A * A * hW)]
    linear_combination (1 + A' * W) * hA + (uL j ^ bb j * vL j) * c1 - eL * hBq +
      (eL * A' - (uL j ^ bb j * vL j) * (bb j : Mod K (n + 1)) * A * B) * hW
  · linear_combination (1 + (A + B') * W + B' * A * W * W) * hD + c2 +
      (dL * (A + B') + B' * A + dL * B' * A * W) * hW

private theorem cgY_succ_of_proj (m : ℕ) (z : Mod K (m + 1)) (z0 : Mod K m) (hz : proj m z = z0)
    (h0 : cgY m z0 1) : cgY (m + 1) z 1 := by
  obtain ⟨w, hw⟩ := h0
  obtain ⟨w', hw'⟩ := proj_surjective (K := K) m w
  obtain ⟨c, hc⟩ := mod_ker m (z - 1 - Yr K (m + 1) * w') (by
    rw [map_sub, map_sub, map_one, map_mul, proj_root, hw', hz, hw]; ring)
  refine ⟨w' + AdjoinRoot.of _ c * Yr K (m + 1) ^ m, ?_⟩
  linear_combination hc

private theorem cgY_evL (m r k : ℕ) (g : MvPolynomial (Fin 2) K) (hk : k ≠ r) (hg : g ∈ Jcn K r k) :
    cgY m (evL m g) 0 := by
  unfold Jcn at hg
  by_cases h0 : k = 0
  · rw [if_pos h0, Ideal.mem_span_singleton'] at hg
    obtain ⟨h, rfl⟩ := hg
    refine ⟨evL m h, ?_⟩
    simp [evL]
    ring
  · rw [if_neg h0, if_neg hk, Ideal.mem_span_singleton'] at hg
    obtain ⟨h, rfl⟩ := hg
    refine ⟨AdjoinRoot.of _ (tn K) * evL m h, ?_⟩
    simp [evL]
    ring

end Eval

end AllModel

section Glue

variable {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (I : X.IdealSheafData)
    {r : ℕ} (V : Fin (r + 1) → X.Opens)

private lemma rhoc_resc (n : ℕ) (V W : X.Opens) (h : W ≤ V)
    (a : Γ(Sc I (n + 1), trc I (n + 1) V)) :
    rhoc I n W (resc I (n + 1) V W h a) = resc I n V W h (rhoc I n V a) := by
  let inc := Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
      (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))
  have h1 : trc I (n + 1) W ≤ trc I (n + 1) V := Scheme.Hom.preimage_mono _ h
  have h2 : trc I n W ≤ trc I n V := Scheme.Hom.preimage_mono _ h
  have hV : trc I n V ≤ inc ⁻¹ᵁ trc I (n + 1) V := by
    simp only [trc, ← Scheme.Hom.comp_preimage, inc, Scheme.IdealSheafData.inclusion_subschemeι,
      le_refl]
  have hW : trc I n W ≤ inc ⁻¹ᵁ trc I (n + 1) W := by
    simp only [trc, ← Scheme.Hom.comp_preimage, inc, Scheme.IdealSheafData.inclusion_subschemeι,
      le_refl]
  have key : (Sc I (n + 1)).presheaf.map (homOfLE h1).op ≫
      inc.appLE (trc I (n + 1) W) (trc I n W) hW =
      inc.appLE (trc I (n + 1) V) (trc I n V) hV ≫
        (Sc I n).presheaf.map (homOfLE h2).op := by
    simp
  exact congrArg (fun f => CommRingCat.Hom.hom f a) key

private lemma appLE_congr_hom {S Y : Scheme.{u}} {F G : S ⟶ Y} (hFG : F = G) (U : Y.Opens)
    (V : S.Opens) (e : V ≤ F ⁻¹ᵁ U) (e' : V ≤ G ⁻¹ᵁ U) : F.appLE U V e = G.appLE U V e' := by
  subst hFG
  rfl

private lemma rhoc_sigc (n : ℕ) (V : X.Opens) (k : K) :
    rhoc I n V (sigc sX I (n + 1) (trc I (n + 1) V) k) = sigc sX I n (trc I n V) k := by
  let inc := Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
      (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))
  have hV : trc I n V ≤ inc ⁻¹ᵁ trc I (n + 1) V := by
    simp only [trc, ← Scheme.Hom.comp_preimage, inc, Scheme.IdealSheafData.inclusion_subschemeι,
      le_refl]
  have hf : inc ≫ (I ^ (n + 1 + 1)).subschemeι ≫ sX = (I ^ (n + 1)).subschemeι ≫ sX := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  have key : ((I ^ (n + 1 + 1)).subschemeι ≫ sX).appLE ⊤ (trc I (n + 1) V) le_top ≫
      inc.appLE (trc I (n + 1) V) (trc I n V) hV =
      ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ (trc I n V) le_top := by
    refine (Scheme.Hom.appLE_comp_appLE inc ((I ^ (n + 1 + 1)).subschemeι ≫ sX) ⊤
      (trc I (n + 1) V) (trc I n V) le_top hV).trans ?_
    exact appLE_congr_hom hf _ _ _ _
  exact congrArg (fun f => CommRingCat.Hom.hom f ((Scheme.ΓSpecIso (.of K)).inv.hom k)) key

private lemma overlap_model (m : ℕ) (j : Fin r) (xm ym : ∀ j, Γ(Sc I m, trc I m (V j)))
    (hpres : PresAt sX I V m xm ym) (hov : OvAt I V m xm ym) :
    ∃ Θ : Mod K m ≃+* Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)),
      Θ (AdjoinRoot.of _ (LaurentPolynomial.T 1)) =
        resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (xm j.castSucc) ∧
      Θ (AdjoinRoot.root _) = resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (ym j.castSucc) ∧
      ∀ k, Θ (AdjoinRoot.of _ (LaurentPolynomial.C k)) =
        resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left
          (sigc sX I m (trc I m (V j.castSucc)) k) := by
  let _ : Algebra Γ(Sc I m, trc I m (V j.castSucc)) Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)) :=
    (resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left).toAlgebra
  have _ : IsLocalization.Away (xm j.castSucc) Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)) :=
    (hpres j.castSucc).1.isLocalization_of_eq_basicOpen (xm j.castSucc)
      (homOfLE (show trc I m (V j.castSucc ⊓ V j.succ) ≤ trc I m (V j.castSucc) from
        Scheme.Hom.preimage_mono _ inf_le_left))
      (hov j).1
  have hJ : Jc (K := K) r j.castSucc = Ideal.span {MvPolynomial.X 1} ∨
      Jc (K := K) r j.castSucc = Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1} := by
    have hne : j.castSucc ≠ Fin.last r := Fin.castSucc_lt_last j |>.ne
    unfold Jc
    by_cases h0 : j.castSucc = 0
    · left; simp [h0]
    · right; simp [h0, hne]
  exact model_level (A := Γ(Sc I m, trc I m (V j.castSucc)))
    (B := Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ))) (sigc sX I m (trc I m (V j.castSucc)))
    (xm j.castSucc) (ym j.castSucc) m (Jc r j.castSucc) hJ (hpres j.castSucc).2.1
    (hpres j.castSucc).2.2

end Glue

section Units

variable {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (I : X.IdealSheafData)
    {r : ℕ} (V : Fin (r + 1) → X.Opens)

/-- The ratios `x_{j+1} / (x_j ^ b_j y_j)` of the initial coordinates on the overlaps, at level
`m`: units. -/
private def RatioAt (b : Fin r → ℕ) (m : ℕ) (xm ym : ∀ j, Γ(Sc I m, trc I m (V j)))
    (rm : ∀ j : Fin r, Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ))) : Prop :=
  ∀ j : Fin r, IsUnit (rm j) ∧
    resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (xm j.succ) =
      rm j * (resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (xm j.castSucc) ^ b j *
        resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (ym j.castSucc))

/-- The multiplicative transition equations for the unit factors `um`, `vm` at level `m`:
`u_{j+1} r_j = u_j ^ b_j v_j` and `(y_{j+1} x_j) v_{j+1} u_j = 1` on the overlap `j`. -/
private def UnitEqAt (b : Fin r → ℕ) (m : ℕ) (xm ym : ∀ j, Γ(Sc I m, trc I m (V j)))
    (rm : ∀ j : Fin r, Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)))
    (um vm : ∀ j, Γ(Sc I m, trc I m (V j))) : Prop :=
  ∀ j : Fin r,
    resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (um j.succ) * rm j =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (um j.castSucc) ^ b j *
        resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (vm j.castSucc) ∧
    (resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (ym j.succ) *
        resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (xm j.castSucc)) *
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (vm j.succ) *
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (um j.castSucc) = 1

/-- Unit factors `u`, `v` solving the multiplicative system up to level `N`. -/
private def UnitSol (b : Fin r → ℕ) (x0 y0 : ∀ j m, Γ(Sc I m, trc I m (V j)))
    (rr : ∀ m, ∀ j : Fin r, Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ))) (N : ℕ)
    (uu vv : ∀ j m, Γ(Sc I m, trc I m (V j))) : Prop :=
  (∀ m ≤ N, ∀ j, IsUnit (uu j m) ∧ IsUnit (vv j m)) ∧
  (∀ m < N, CompatAt I V m (fun j => uu j (m + 1)) (fun j => uu j m) ∧
    CompatAt I V m (fun j => vv j (m + 1)) (fun j => vv j m)) ∧
  (∀ m ≤ N, UnitEqAt I V b m (fun j => x0 j m) (fun j => y0 j m) (rr m)
    (fun j => uu j m) (fun j => vv j m)) ∧
  (∀ m ≤ N, ∀ j, (∃ p, p - 1 ∈ Jc r j ∧
      MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V j))) ![x0 j m, y0 j m] p = uu j m) ∧
    ∃ p, p - 1 ∈ Jc r j ∧
      MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V j))) ![x0 j m, y0 j m] p = vv j m)

private lemma jc_eq (j : Fin (r + 1)) : ∃ g : MvPolynomial (Fin 2) K, Jc r j = Ideal.span {g} ∧
    (g = MvPolynomial.X 1 ∨ g = MvPolynomial.X 0 * MvPolynomial.X 1 ∨ g = MvPolynomial.X 0) := by
  unfold Jc
  split_ifs
  · exact ⟨_, rfl, Or.inl rfl⟩
  · exact ⟨_, rfl, Or.inr (Or.inr rfl)⟩
  · exact ⟨_, rfl, Or.inr (Or.inl rfl)⟩

/-- Scaling the coordinates by units congruent to `1` modulo the exceptional ideal keeps the
presentation of the chart by `𝔸²` along `Jc`. -/
private lemma presAt_mul_isUnit (m : ℕ) (xm ym um vm : ∀ j, Γ(Sc I m, trc I m (V j)))
    (hpres : PresAt sX I V m xm ym)
    (hu : ∀ j, ∃ p, p - 1 ∈ Jc r j ∧
      MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V j))) ![xm j, ym j] p = um j)
    (hv : ∀ j, ∃ p, p - 1 ∈ Jc r j ∧
      MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V j))) ![xm j, ym j] p = vm j) :
    PresAt sX I V m (fun j => xm j * um j) (fun j => ym j * vm j) := by
  intro j
  obtain ⟨hA, hs, hk⟩ := hpres j
  obtain ⟨g, hJ, hg⟩ := jc_eq (K := K) (r := r) j
  obtain ⟨pu, hpu, hpu'⟩ := hu j
  obtain ⟨pv, hpv, hpv'⟩ := hv j
  obtain ⟨h1, h2⟩ := presentation_mul_unit (sigc sX I m (trc I m (V j))) (xm j) (ym j) (um j)
    (vm j) (Jc r j) g hJ hg (m + 1) hk pu pv hpu hpv hpu' hpv'
  exact ⟨hA, h2 hs, h1⟩

end Units

section Ratio

variable {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (I : X.IdealSheafData)
    {r : ℕ} (V : Fin (r + 1) → X.Opens)

private lemma overlap_compat (m : ℕ) (j : Fin r)
    (x1 y1 : ∀ j, Γ(Sc I (m + 1), trc I (m + 1) (V j)))
    (x0 y0 : ∀ j, Γ(Sc I m, trc I m (V j)))
    (hx : CompatAt I V m x1 x0) (hy : CompatAt I V m y1 y0)
    (Θ1 : Mod K (m + 1) ≃+* Γ(Sc I (m + 1), trc I (m + 1) (V j.castSucc ⊓ V j.succ)))
    (Θ0 : Mod K m ≃+* Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)))
    (h1T : Θ1 (AdjoinRoot.of _ (LaurentPolynomial.T 1)) =
      resc I (m + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left (x1 j.castSucc))
    (h1Y : Θ1 (AdjoinRoot.root _) =
      resc I (m + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left (y1 j.castSucc))
    (h1C : ∀ k, Θ1 (AdjoinRoot.of _ (LaurentPolynomial.C k)) =
      resc I (m + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left
        (sigc sX I (m + 1) (trc I (m + 1) (V j.castSucc)) k))
    (h0T : Θ0 (AdjoinRoot.of _ (LaurentPolynomial.T 1)) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (x0 j.castSucc))
    (h0Y : Θ0 (AdjoinRoot.root _) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (y0 j.castSucc))
    (h0C : ∀ k, Θ0 (AdjoinRoot.of _ (LaurentPolynomial.C k)) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left
        (sigc sX I m (trc I m (V j.castSucc)) k))
    (z : Mod K (m + 1)) :
    rhoc I m _ (Θ1 z) = Θ0 (proj m z) := by
  let f : Mod K (m + 1) →+* Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)) :=
    (rhoc I m (V j.castSucc ⊓ V j.succ)).comp Θ1.toRingHom
  let g : Mod K (m + 1) →+* Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)) :=
    Θ0.toRingHom.comp (proj m)
  have key : f = g := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · refine laurent_hom_ext _ _ (fun k => ?_) ?_
      · show rhoc I m _ (Θ1 (AdjoinRoot.of _ (LaurentPolynomial.C k))) =
          Θ0 (proj m (AdjoinRoot.of _ (LaurentPolynomial.C k)))
        rw [h1C, proj_of, h0C]
        have := rhoc_resc I m (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left
          (sigc sX I (m + 1) (trc I (m + 1) (V j.castSucc)) k)
        rwa [rhoc_sigc] at this
      · show rhoc I m _ (Θ1 (AdjoinRoot.of _ (LaurentPolynomial.T 1))) =
          Θ0 (proj m (AdjoinRoot.of _ (LaurentPolynomial.T 1)))
        rw [h1T, proj_of, h0T, rhoc_resc, hx j.castSucc]
    · show rhoc I m _ (Θ1 (AdjoinRoot.root _)) = Θ0 (proj m (AdjoinRoot.root _))
      rw [h1Y, proj_root, h0Y, rhoc_resc, hy j.castSucc]
  exact congrArg (fun F => F z) key

/-- The ratios of the initial coordinates `x_{j+1} / (x_j ^ b_j y_j)` exist, compatibly in the
level, with `rr 0 = 1`. -/
private lemma exists_ratio (b : Fin r → ℕ)
    (x0 y0 : ∀ j m, Γ(Sc I m, trc I m (V j)))
    (hpres : ∀ m, PresAt sX I V m (fun j => x0 j m) (fun j => y0 j m))
    (hov : ∀ m, OvAt I V m (fun j => x0 j m) (fun j => y0 j m))
    (hcomp : ∀ m, CompatAt I V m (fun j => x0 j (m + 1)) (fun j => x0 j m) ∧
      CompatAt I V m (fun j => y0 j (m + 1)) (fun j => y0 j m))
    (hX1 : TransXAt I V b 1 (fun j => x0 j 1) (fun j => y0 j 1)) :
    ∃ rr : ∀ m, ∀ j : Fin r, Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)),
      (∀ m, RatioAt I V b m (fun j => x0 j m) (fun j => y0 j m) (rr m)) ∧
      (∀ m j, rhoc I m _ (rr (m + 1) j) = rr m j) ∧ ∀ j, rr 0 j = 1 := by
  choose Θ hΘ using fun (m : ℕ) (j : Fin r) =>
    overlap_model sX I V m j (fun j => x0 j m) (fun j => y0 j m) (hpres m) (hov m)
  have hcompΘ : ∀ m j z, rhoc I m _ (Θ (m + 1) j z) = Θ m j (proj m z) := fun m j z =>
    overlap_compat sX I V m j (fun j => x0 j (m + 1)) (fun j => y0 j (m + 1))
      (fun j => x0 j m) (fun j => y0 j m) (hcomp m).1 (hcomp m).2 (Θ (m + 1) j) (Θ m j)
      (hΘ (m + 1) j).1 (hΘ (m + 1) j).2.1 (hΘ (m + 1) j).2.2 (hΘ m j).1 (hΘ m j).2.1
      (hΘ m j).2.2 z
  have hrat : ∀ j : Fin r, ∃ c : ∀ m, Mod K m, (∀ m, IsUnit (c m)) ∧
      (∀ m, (Θ m j).symm (resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (x0 j.succ m)) =
        c m * ((AdjoinRoot.of _ (LaurentPolynomial.T 1)) ^ (b j) * Yr K m)) ∧
      (∀ m, proj m (c (m + 1)) = c m) ∧ c 0 = 1 := by
    intro j
    refine ratio_exists_mod (b j)
      (fun m => (Θ m j).symm (resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (x0 j.succ m)))
      (fun m => ?_) ?_
    · rw [RingEquiv.eq_symm_apply, ← hcompΘ, RingEquiv.apply_symm_apply, rhoc_resc]
      rw [(hcomp m).1 j.succ]
    · rw [RingEquiv.symm_apply_eq, map_mul, map_pow, (hΘ 1 j).1, (hΘ 1 j).2.1]
      exact hX1 j
  choose c hc using hrat
  refine ⟨fun m j => Θ m j (c j m), fun m j => ⟨(hc j).1 m |>.map _, ?_⟩, fun m j => ?_,
    fun j => ?_⟩
  · have h := ((hc j).2.1 m)
    rw [RingEquiv.symm_apply_eq, map_mul, map_mul, map_pow, (hΘ m j).1, (hΘ m j).2.1] at h
    exact h
  · show rhoc I m _ (Θ (m + 1) j (c j (m + 1))) = Θ m j (c j m)
    rw [hcompΘ, (hc j).2.2.1]
  · show Θ 0 j (c j 0) = 1
    rw [(hc j).2.2.2, map_one]

end Ratio

section Step

variable {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (I : X.IdealSheafData)
    {r : ℕ} (V : Fin (r + 1) → X.Opens)

private lemma sigc_resc (n : ℕ) (V W : X.Opens) (h : W ≤ V) (k : K) :
    resc I n V W h (sigc sX I n (trc I n V) k) = sigc sX I n (trc I n W) k := by
  have h1 : trc I n W ≤ trc I n V := Scheme.Hom.preimage_mono _ h
  have key : ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ (trc I n V) le_top ≫
      (Sc I n).presheaf.map (homOfLE h1).op =
      ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ (trc I n W) le_top :=
    Scheme.Hom.appLE_map _ _ _
  exact congrArg (fun f => CommRingCat.Hom.hom f ((Scheme.ΓSpecIso (.of K)).inv.hom k)) key

private lemma rhoc_eval (n : ℕ) (V : X.Opens) (x1 y1 : Γ(Sc I (n + 1), trc I (n + 1) V))
    (x0 y0 : Γ(Sc I n, trc I n V)) (hx : rhoc I n V x1 = x0) (hy : rhoc I n V y1 = y0)
    (P : MvPolynomial (Fin 2) K) :
    rhoc I n V (MvPolynomial.eval₂Hom (sigc sX I (n + 1) (trc I (n + 1) V)) ![x1, y1] P) =
      MvPolynomial.eval₂Hom (sigc sX I n (trc I n V)) ![x0, y0] P := by
  have : (rhoc I n V).comp (MvPolynomial.eval₂Hom (sigc sX I (n + 1) (trc I (n + 1) V)) ![x1,
      y1]) =
      MvPolynomial.eval₂Hom (sigc sX I n (trc I n V)) ![x0, y0] := by
    refine MvPolynomial.ringHom_ext (fun k => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact rhoc_sigc sX I n V k
    · fin_cases i
      · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero]
        exact hx
      · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one,
          Matrix.head_cons]
        exact hy
  exact congrArg (fun f => f P) this

private lemma theta_evL (m : ℕ) (j : Fin r) (xm ym : ∀ j, Γ(Sc I m, trc I m (V j)))
    (Θ : Mod K m ≃+* Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)))
    (hT : Θ (AdjoinRoot.of _ (LaurentPolynomial.T 1)) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (xm j.castSucc))
    (hY : Θ (AdjoinRoot.root _) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (ym j.castSucc))
    (hC : ∀ k, Θ (AdjoinRoot.of _ (LaurentPolynomial.C k)) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left
        (sigc sX I m (trc I m (V j.castSucc)) k))
    (P : MvPolynomial (Fin 2) K) :
    Θ (evL m P) = resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left
      (MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V j.castSucc))) ![xm j.castSucc, ym j.castSucc]
        P) := by
  have : Θ.toRingHom.comp (evL m) = (resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left).comp
      (MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V j.castSucc)))
        ![xm j.castSucc, ym j.castSucc]) := by
    refine MvPolynomial.ringHom_ext (fun k => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, evL, MvPolynomial.eval₂Hom_C]
      exact hC k
    · fin_cases i
      · simp only [RingHom.comp_apply, evL, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero]
        exact hT
      · simp only [RingHom.comp_apply, evL, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one,
          Matrix.head_cons]
        exact hY
  exact congrArg (fun f => f P) this

private lemma theta_evR (m : ℕ) (j : Fin r) (xm ym : ∀ j, Γ(Sc I m, trc I m (V j)))
    (rr : Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)))
    (Θ : Mod K m ≃+* Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)))
    (hT : Θ (AdjoinRoot.of _ (LaurentPolynomial.T 1)) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (xm j.castSucc))
    (hY : Θ (AdjoinRoot.root _) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (ym j.castSucc))
    (hC : ∀ k, Θ (AdjoinRoot.of _ (LaurentPolynomial.C k)) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left
        (sigc sX I m (trc I m (V j.castSucc)) k))
    (b : ℕ) (cc ss : Mod K m) (hcc : Θ cc = rr)
    (hrat : resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (xm j.succ) =
      rr * (resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (xm j.castSucc) ^ b *
        resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (ym j.castSucc)))
    (hss : Θ ss = resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (ym j.succ) *
        resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (xm j.castSucc))
    (P : MvPolynomial (Fin 2) K) :
    Θ (evR m cc ss b P) = resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right
      (MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V j.succ))) ![xm j.succ, ym j.succ] P) := by
  have hTi : Θ (AdjoinRoot.of _ (ti K)) *
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (xm j.castSucc) = 1 := by
    rw [← hT, ← map_mul, mul_comm, ofL_tn_mul_ti, map_one]
  have : Θ.toRingHom.comp (evR m cc ss b) =
      (resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right).comp
      (MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V j.succ))) ![xm j.succ, ym j.succ]) := by
    refine MvPolynomial.ringHom_ext (fun k => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, evR, MvPolynomial.eval₂Hom_C]
      have h : Θ (σMod K m k) = resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left
          (sigc sX I m (trc I m (V j.castSucc)) k) := hC k
      refine h.trans ?_
      show resc I m _ _ inf_le_left (sigc sX I m (trc I m (V j.castSucc)) k) =
        resc I m _ _ inf_le_right (sigc sX I m (trc I m (V j.succ)) k)
      rw [sigc_resc, sigc_resc]
    · fin_cases i
      · simp only [RingHom.comp_apply, evR, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero]
        show Θ (cc * _ ^ b * _) = resc I m _ _ inf_le_right (xm j.succ)
        rw [map_mul, map_mul, map_pow, hcc, hT, hY, hrat]
        ring
      · simp only [RingHom.comp_apply, evR, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one,
          Matrix.head_cons]
        show Θ (ss * _) = resc I m _ _ inf_le_right (ym j.succ)
        rw [map_mul, hss]
        linear_combination (resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (ym j.succ)) * hTi
  exact congrArg (fun f => f P) this

/-- The specification of the model isomorphism of the overlap `j` at level `m`. -/
private def ThetaSpec (m : ℕ) (j : Fin r) (xm ym : ∀ j, Γ(Sc I m, trc I m (V j)))
    (Θ : Mod K m ≃+* Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ))) : Prop :=
  Θ (AdjoinRoot.of _ (LaurentPolynomial.T 1)) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (xm j.castSucc) ∧
    Θ (AdjoinRoot.root _) = resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (ym j.castSucc) ∧
    ∀ k, Θ (AdjoinRoot.of _ (LaurentPolynomial.C k)) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left
        (sigc sX I m (trc I m (V j.castSucc)) k)

private lemma proj_symm (n : ℕ) (j : Fin r)
    (Θ1 : Mod K (n + 1) ≃+* Γ(Sc I (n + 1), trc I (n + 1) (V j.castSucc ⊓ V j.succ)))
    (Θ0 : Mod K n ≃+* Γ(Sc I n, trc I n (V j.castSucc ⊓ V j.succ)))
    (hc : ∀ z, rhoc I n _ (Θ1 z) = Θ0 (proj n z))
    (z1 : Γ(Sc I (n + 1), trc I (n + 1) (V j.castSucc ⊓ V j.succ)))
    (z0 : Γ(Sc I n, trc I n (V j.castSucc ⊓ V j.succ))) (h : rhoc I n _ z1 = z0) :
    proj n (Θ1.symm z1) = Θ0.symm z0 := by
  rw [RingEquiv.eq_symm_apply, ← hc, RingEquiv.apply_symm_apply, h]

private lemma overlap_package (j : Fin r) (x0 y0 : ∀ j m, Γ(Sc I m, trc I m (V j)))
    (hpres : ∀ m, PresAt sX I V m (fun j => x0 j m) (fun j => y0 j m))
    (hov : ∀ m, OvAt I V m (fun j => x0 j m) (fun j => y0 j m))
    (hcomp : ∀ m, CompatAt I V m (fun j => x0 j (m + 1)) (fun j => x0 j m) ∧
      CompatAt I V m (fun j => y0 j (m + 1)) (fun j => y0 j m))
    (hY0 : TransYAt I V 0 (fun j => x0 j 0) (fun j => y0 j 0))
    (rr : ∀ m, ∀ j : Fin r, Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)))
    (hrcomp : ∀ m j, rhoc I m _ (rr (m + 1) j) = rr m j) (hr0 : ∀ j, rr 0 j = 1) (n : ℕ) :
    ∃ (Θ1 : Mod K (n + 1) ≃+* Γ(Sc I (n + 1), trc I (n + 1) (V j.castSucc ⊓ V j.succ)))
      (Θ0 : Mod K n ≃+* Γ(Sc I n, trc I n (V j.castSucc ⊓ V j.succ))),
      ThetaSpec sX I V (n + 1) j (fun j => x0 j (n + 1)) (fun j => y0 j (n + 1)) Θ1 ∧
      ThetaSpec sX I V n j (fun j => x0 j n) (fun j => y0 j n) Θ0 ∧
      (∀ z, rhoc I n _ (Θ1 z) = Θ0 (proj n z)) ∧
      cgY (n + 1) (Θ1.symm (rr (n + 1) j)) 1 ∧
      cgY (n + 1) (Θ1.symm (resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_right
          (y0 j.succ (n + 1)) *
        resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left (x0 j.castSucc (n + 1)))) 1 := by
  have hsc : ∀ m, rhoc I m _ (resc I (m + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_right
        (y0 j.succ (m + 1)) *
      resc I (m + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left (x0 j.castSucc (m + 1))) =
      resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_right (y0 j.succ m) *
        resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (x0 j.castSucc m) := by
    intro m
    rw [map_mul, rhoc_resc, rhoc_resc, (hcomp m).2 j.succ, (hcomp m).1 j.castSucc]
  induction n with
  | zero =>
    obtain ⟨Θ0, h0⟩ := overlap_model sX I V 0 j (fun j => x0 j 0) (fun j => y0 j 0) (hpres 0) (hov
        0)
    obtain ⟨Θ1, h1⟩ := overlap_model sX I V 1 j (fun j => x0 j 1) (fun j => y0 j 1) (hpres 1) (hov
        1)
    have hc : ∀ z, rhoc I 0 _ (Θ1 z) = Θ0 (proj 0 z) := fun z =>
      overlap_compat sX I V 0 j (fun j => x0 j 1) (fun j => y0 j 1) (fun j => x0 j 0)
        (fun j => y0 j 0) (hcomp 0).1 (hcomp 0).2 Θ1 Θ0 h1.1 h1.2.1 h1.2.2 h0.1 h0.2.1 h0.2.2 z
    refine ⟨Θ1, Θ0, h1, h0, hc, ?_, ?_⟩
    · refine cgY_succ_of_proj 0 _ (Θ0.symm (rr 0 j)) (proj_symm I V 0 j Θ1 Θ0 hc _ _
        (hrcomp 0 j)) ?_
      rw [hr0 j, map_one]; exact cgY_refl 0 1
    · refine cgY_succ_of_proj 0 _ (Θ0.symm (resc I 0 _ (V j.castSucc ⊓ V j.succ) inf_le_right
        (y0 j.succ 0) * resc I 0 _ (V j.castSucc ⊓ V j.succ) inf_le_left (x0 j.castSucc 0)))
        (proj_symm I V 0 j Θ1 Θ0 hc _ _ (hsc 0)) ?_
      have := hY0 j
      simp only at this
      rw [this, map_one]; exact cgY_refl 0 1
  | succ n ih =>
    obtain ⟨Θ1, Θ0, h1, h0, hc, hcr, hcs⟩ := ih
    obtain ⟨Θ2, h2⟩ := overlap_model sX I V (n + 2) j (fun j => x0 j (n + 2)) (fun j => y0 j (n +
        2))
      (hpres (n + 2)) (hov (n + 2))
    have hc2 : ∀ z, rhoc I (n + 1) _ (Θ2 z) = Θ1 (proj (n + 1) z) := fun z =>
      overlap_compat sX I V (n + 1) j (fun j => x0 j (n + 2)) (fun j => y0 j (n + 2))
        (fun j => x0 j (n + 1)) (fun j => y0 j (n + 1)) (hcomp (n + 1)).1 (hcomp (n + 1)).2 Θ2 Θ1
        h2.1 h2.2.1 h2.2.2 h1.1 h1.2.1 h1.2.2 z
    refine ⟨Θ2, Θ1, h2, h1, hc2, ?_, ?_⟩
    · exact cgY_succ_of_proj (n + 1) _ _ (proj_symm I V (n + 1) j Θ2 Θ1 hc2 _ _
        (hrcomp (n + 1) j)) hcr
    · exact cgY_succ_of_proj (n + 1) _ _ (proj_symm I V (n + 1) j Θ2 Θ1 hc2 _ _
        (hsc (n + 1))) hcs

/-- Junk-extension of a family on `Fin r` to `ℕ`. -/
private def extN {α : Type*} (r : ℕ) (G : Fin r → α) (d : α) : ℕ → α := fun j =>
  if hj : j < r then G ⟨j, hj⟩ else d

private lemma extN_val {α : Type*} (r : ℕ) (G : Fin r → α) (d : α) (j : Fin r) :
    extN r G d j.val = G j := by
  simp [extN, j.isLt]

private lemma cgY_extN {m : ℕ} (G : Fin r → Mod K m) (hG : ∀ j, cgY m (G j) 1) (j : ℕ) :
    cgY m (extN r G 1 j) 1 := by
  unfold extN
  split_ifs
  · exact hG _
  · exact cgY_refl _ _

private lemma Jc_eq_Jcn (j : Fin (r + 1)) : Jc (K := K) r j = Jcn K r j.val := by
  unfold Jc Jcn
  have h0 : (j = 0) ↔ (j.val = 0) := ⟨by rintro rfl; rfl, fun h => Fin.ext h⟩
  have hl : (j = Fin.last r) ↔ (j.val = r) := ⟨by rintro rfl; rfl, fun h => Fin.ext h⟩
  simp only [h0, hl]

private lemma cgY_evL_one (m : ℕ) (k : Fin (r + 1)) (hk : k.val ≠ r) (p : MvPolynomial (Fin 2) K)
    (hp : p - 1 ∈ Jc (K := K) r k) : cgY m (evL m p) 1 := by
  rw [Jc_eq_Jcn] at hp
  obtain ⟨w, hw⟩ := cgY_evL m r k.val (p - 1) hk hp
  refine ⟨w, ?_⟩
  rw [show evL m p = evL m (p - 1) + 1 by rw [map_sub, map_one, sub_add_cancel], hw]
  ring

private lemma isUnit_eval_of_sub_one_mem (m : ℕ) (k : Fin (r + 1))
    (xm ym : ∀ j, Γ(Sc I m, trc I m (V j)))
    (hpres : PresAt sX I V m xm ym) (p : MvPolynomial (Fin 2) K) (hp : p - 1 ∈ Jc (K := K) r k) :
    IsUnit (MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V k))) ![xm k, ym k] p) := by
  have hker := (hpres k).2.2
  have hnil : IsNilpotent (MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V k))) ![xm k, ym k]
      (p - 1)) := by
    refine ⟨m + 1, ?_⟩
    rw [← map_pow, ← RingHom.mem_ker, hker]
    exact Ideal.pow_mem_pow hp (m + 1)
  have : MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V k))) ![xm k, ym k] p =
      1 + MvPolynomial.eval₂Hom (sigc sX I m (trc I m (V k))) ![xm k, ym k] (p - 1) := by
    rw [map_sub, map_one]; ring
  rw [this]
  exact IsNilpotent.isUnit_one_add hnil

private lemma new_sub_one_mem (n : ℕ) (k : Fin (r + 1)) (p f : MvPolynomial (Fin 2) K)
    (hp : p - 1 ∈ Jc (K := K) r k) (hf : f ∈ Jc (K := K) r k ^ (n + 1)) :
    p * (1 + f) - 1 ∈ Jc (K := K) r k := by
  have hf' : f ∈ Jc (K := K) r k := Ideal.pow_le_self (Nat.succ_ne_zero n) hf
  have : p * (1 + f) - 1 = (p - 1) + p * f := by ring
  rw [this]
  exact Ideal.add_mem _ hp (Ideal.mul_mem_left _ _ hf')

/-- The correction step on unit factors: the obstruction to lifting a solution of the
multiplicative system from level `n` to level `n + 1` is a Čech `1`-cochain of `J_{n+1}` on the
chain, which is solved explicitly along the chain in the model of the overlaps. -/
private lemma exists_unitSol_succ (hr : 0 < r) (b : Fin r → ℕ) (hb : ∀ i, 2 ≤ b i)
    (x0 y0 : ∀ j m, Γ(Sc I m, trc I m (V j)))
    (hpres : ∀ m, PresAt sX I V m (fun j => x0 j m) (fun j => y0 j m))
    (hov : ∀ m, OvAt I V m (fun j => x0 j m) (fun j => y0 j m))
    (hcomp : ∀ m, CompatAt I V m (fun j => x0 j (m + 1)) (fun j => x0 j m) ∧
      CompatAt I V m (fun j => y0 j (m + 1)) (fun j => y0 j m))
    (hY0 : TransYAt I V 0 (fun j => x0 j 0) (fun j => y0 j 0))
    (rr : ∀ m, ∀ j : Fin r, Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)))
    (hrat : ∀ m, RatioAt I V b m (fun j => x0 j m) (fun j => y0 j m) (rr m))
    (hrcomp : ∀ m j, rhoc I m _ (rr (m + 1) j) = rr m j) (hr0 : ∀ j, rr 0 j = 1)
    (n : ℕ) (uu vv : ∀ j m, Γ(Sc I m, trc I m (V j)))
    (h : UnitSol sX I V b x0 y0 rr n uu vv) :
    ∃ u' v' : ∀ j m, Γ(Sc I m, trc I m (V j)), UnitSol sX I V b x0 y0 rr (n + 1) u' v' ∧
      ∀ j m, m ≤ n → u' j m = uu j m ∧ v' j m = vv j m := by
  obtain ⟨hunit, hcompu, heq, hone⟩ := h
  -- the polynomials of the units at level `n`
  have hpu : ∀ k : Fin (r + 1), ∃ pu pv : MvPolynomial (Fin 2) K,
      (pu - 1 ∈ Jc r k ∧ MvPolynomial.eval₂Hom (sigc sX I n (trc I n (V k))) ![x0 k n, y0 k n] pu =
        uu k n) ∧
      (pv - 1 ∈ Jc r k ∧ MvPolynomial.eval₂Hom (sigc sX I n (trc I n (V k))) ![x0 k n, y0 k n] pv =
        vv k n) := by
    intro k
    obtain ⟨⟨pu, h1, h2⟩, ⟨pv, h3, h4⟩⟩ := hone n le_rfl k
    exact ⟨pu, pv, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
  choose pu pv hpuv using hpu
  -- the overlap models
  have hpk := fun j : Fin r => overlap_package sX I V j x0 y0 hpres hov hcomp hY0 rr hrcomp hr0 n
  choose Θ1 Θ0 hs1 hs0 hcΘ hcr hcs using hpk
  let ccF : Fin r → Mod K (n + 1) := fun j => (Θ1 j).symm (rr (n + 1) j)
  let ssF : Fin r → Mod K (n + 1) := fun j => (Θ1 j).symm
    (resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_right (y0 j.succ (n + 1)) *
      resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left (x0 j.castSucc (n + 1)))
  let uLF : Fin r → Mod K (n + 1) := fun j => evL (n + 1) (pu j.castSucc)
  let vLF : Fin r → Mod K (n + 1) := fun j => evL (n + 1) (pv j.castSucc)
  let uRF : Fin r → Mod K (n + 1) := fun j =>
    evR (n + 1) (ccF j) (ssF j) (b j) (pu j.succ)
  let vRF : Fin r → Mod K (n + 1) := fun j =>
    evR (n + 1) (ccF j) (ssF j) (b j) (pv j.succ)
  have hcc := cgY_extN ccF hcr
  have hss := cgY_extN ssF hcs
  have huL := cgY_extN uLF fun j =>
    cgY_evL_one _ _ (by simp; omega) _ (hpuv _).1.1
  have hvL := cgY_extN vLF fun j =>
    cgY_evL_one _ _ (by simp; omega) _ (hpuv _).2.1
  -- the lifts of the units to level `n + 1`
  let ev : ∀ k : Fin (r + 1), MvPolynomial (Fin 2) K →+*
      Γ(Sc I (n + 1), trc I (n + 1) (V k)) := fun k =>
    MvPolynomial.eval₂Hom (sigc sX I (n + 1) (trc I (n + 1) (V k))) ![x0 k (n + 1), y0 k (n + 1)]
  have hrho : ∀ (k : Fin (r + 1)) (P : MvPolynomial (Fin 2) K),
      rhoc I n (V k) (ev k P) =
        MvPolynomial.eval₂Hom (sigc sX I n (trc I n (V k))) ![x0 k n, y0 k n] P := fun k P =>
    rhoc_eval sX I n (V k) _ _ _ _ ((hcomp n).1 k) ((hcomp n).2 k) P
  have hLu : ∀ (j : Fin r) (P : MvPolynomial (Fin 2) K),
      Θ1 j (evL (n + 1) P) = resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left
        (ev j.castSucc P) := fun j P =>
    theta_evL sX I V (n + 1) j (fun j => x0 j (n + 1)) (fun j => y0 j (n + 1)) (Θ1 j)
      (hs1 j).1 (hs1 j).2.1 (hs1 j).2.2 P
  have hRu : ∀ (j : Fin r) (P : MvPolynomial (Fin 2) K),
      Θ1 j (evR (n + 1) (ccF j) (ssF j) (b j) P) =
        resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_right (ev j.succ P) := fun j P =>
    theta_evR sX I V (n + 1) j (fun j => x0 j (n + 1)) (fun j => y0 j (n + 1)) (rr (n + 1) j)
      (Θ1 j) (hs1 j).1 (hs1 j).2.1 (hs1 j).2.2 (b j) (ccF j) (ssF j)
      (RingEquiv.apply_symm_apply _ _) ((hrat (n + 1) j).2) (RingEquiv.apply_symm_apply _ _) P
  have hE1 : ∀ j : ℕ, j < r → proj n (extN r uRF 1 j * extN r ccF 1 j) =
      proj n (extN r uLF 1 j ^ (extN r b 2 j) * extN r vLF 1 j) := by
    intro j hj
    obtain ⟨jj, rfl⟩ : ∃ jj : Fin r, jj.val = j := ⟨⟨j, hj⟩, rfl⟩
    simp only [extN_val]
    apply (Θ0 jj).injective
    rw [← hcΘ jj, ← hcΘ jj, map_mul (Θ1 jj), map_mul (Θ1 jj), map_pow (Θ1 jj)]
    have e1 : Θ1 jj (uRF jj) = resc I (n + 1) _ (V jj.castSucc ⊓ V jj.succ) inf_le_right
        (ev jj.succ (pu jj.succ)) := hRu jj _
    have e2 : Θ1 jj (ccF jj) = rr (n + 1) jj := RingEquiv.apply_symm_apply _ _
    have e3 : Θ1 jj (uLF jj) = resc I (n + 1) _ (V jj.castSucc ⊓ V jj.succ) inf_le_left
        (ev jj.castSucc (pu jj.castSucc)) := hLu jj _
    have e4 : Θ1 jj (vLF jj) = resc I (n + 1) _ (V jj.castSucc ⊓ V jj.succ) inf_le_left
        (ev jj.castSucc (pv jj.castSucc)) := hLu jj _
    rw [e1, e2, e3, e4, map_mul (rhoc I n _), map_mul (rhoc I n _), map_pow (rhoc I n _),
      rhoc_resc, rhoc_resc, rhoc_resc,
      hrho, hrho, hrho, (hpuv _).1.2, (hpuv _).1.2, (hpuv _).2.2, hrcomp]
    exact (heq n le_rfl jj).1
  have hE2 : ∀ j : ℕ, j < r → proj n (extN r ssF 1 j * extN r vRF 1 j * extN r uLF 1 j) = 1 := by
    intro j hj
    obtain ⟨jj, rfl⟩ : ∃ jj : Fin r, jj.val = j := ⟨⟨j, hj⟩, rfl⟩
    simp only [extN_val]
    apply (Θ0 jj).injective
    rw [← hcΘ jj, map_mul (Θ1 jj), map_mul (Θ1 jj), map_one]
    have e1 : Θ1 jj (vRF jj) = resc I (n + 1) _ (V jj.castSucc ⊓ V jj.succ) inf_le_right
        (ev jj.succ (pv jj.succ)) := hRu jj _
    have e2 : Θ1 jj (ssF jj) = resc I (n + 1) _ (V jj.castSucc ⊓ V jj.succ) inf_le_right
        (y0 jj.succ (n + 1)) *
        resc I (n + 1) _ (V jj.castSucc ⊓ V jj.succ) inf_le_left (x0 jj.castSucc (n + 1)) :=
      RingEquiv.apply_symm_apply _ _
    have e3 : Θ1 jj (uLF jj) = resc I (n + 1) _ (V jj.castSucc ⊓ V jj.succ) inf_le_left
        (ev jj.castSucc (pu jj.castSucc)) := hLu jj _
    rw [e1, e2, e3, map_mul (rhoc I n _), map_mul (rhoc I n _), map_mul (rhoc I n _),
      rhoc_resc, rhoc_resc, rhoc_resc, rhoc_resc,
      hrho, hrho, (hpuv _).2.2, (hpuv _).1.2, (hcomp n).2 jj.succ, (hcomp n).1 jj.castSucc]
    exact (heq n le_rfl jj).2
  obtain ⟨pα, pβ, qα, qβ, hsol⟩ := solve_M n r hr (extN r b 2) (fun j => by
      by_cases hj : j < r
      · rw [show extN r b 2 j = b ⟨j, hj⟩ from dif_pos hj]; exact hb _
      · rw [show extN r b 2 j = 2 from dif_neg hj]) (extN r ccF 1) (extN r ssF 1) (extN r uRF 1)
    (extN r uLF 1) (extN r vLF 1) (extN r vRF 1) hcc hss huL hvL hE1 hE2
  let fα : Fin (r + 1) → MvPolynomial (Fin 2) K := fun k =>
    fpoly r (n + 1) k.val (pα k.val) (qα k.val)
  let fβ : Fin (r + 1) → MvPolynomial (Fin 2) K := fun k =>
    fpoly r (n + 1) k.val (pβ k.val) (qβ k.val)
  have hfα : ∀ k, fα k ∈ Jc (K := K) r k ^ (n + 1) := fun k => by
    rw [Jc_eq_Jcn]; exact fpoly_mem r (n + 1) k.val _ _
  have hfβ : ∀ k, fβ k ∈ Jc (K := K) r k ^ (n + 1) := fun k => by
    rw [Jc_eq_Jcn]; exact fpoly_mem r (n + 1) k.val _ _
  let unew : ∀ k : Fin (r + 1), Γ(Sc I (n + 1), trc I (n + 1) (V k)) := fun k =>
    ev k (pu k * (1 + fα k))
  let vnew : ∀ k : Fin (r + 1), Γ(Sc I (n + 1), trc I (n + 1) (V k)) := fun k =>
    ev k (pv k * (1 + fβ k))
  let u' : ∀ j m, Γ(Sc I m, trc I m (V j)) := fun j m =>
    if h : m = n + 1 then h ▸ unew j else uu j m
  let v' : ∀ j m, Γ(Sc I m, trc I m (V j)) := fun j m =>
    if h : m = n + 1 then h ▸ vnew j else vv j m
  have u'_new : ∀ j, u' j (n + 1) = unew j := fun j => dif_pos rfl
  have v'_new : ∀ j, v' j (n + 1) = vnew j := fun j => dif_pos rfl
  have u'_old : ∀ j m, m ≠ n + 1 → u' j m = uu j m := fun j m hm => dif_neg hm
  have v'_old : ∀ j m, m ≠ n + 1 → v' j m = vv j m := fun j m hm => dif_neg hm
  refine ⟨u', v', ⟨?_, ?_, ?_, ?_⟩, fun j m hm =>
    ⟨u'_old j m (by omega), v'_old j m (by omega)⟩⟩
  · intro m hm j
    by_cases hmn : m = n + 1
    · subst hmn
      rw [u'_new, v'_new]
      exact ⟨isUnit_eval_of_sub_one_mem sX I V (n + 1) j _ _ (hpres (n + 1)) _
          (new_sub_one_mem n j _ _ (hpuv j).1.1 (hfα j)),
        isUnit_eval_of_sub_one_mem sX I V (n + 1) j _ _ (hpres (n + 1)) _
          (new_sub_one_mem n j _ _ (hpuv j).2.1 (hfβ j))⟩
    · rw [u'_old j m hmn, v'_old j m hmn]; exact hunit m (by omega) j
  · intro m hm
    have hker0 : ∀ (j : Fin (r + 1)) (f : MvPolynomial (Fin 2) K), f ∈ Jc (K := K) r j ^ (n + 1) →
        MvPolynomial.eval₂Hom (sigc sX I n (trc I n (V j))) ![x0 j n, y0 j n] f = 0 := by
      intro j f hf
      rw [← RingHom.mem_ker, (hpres n j).2.2]; exact hf
    by_cases hmn : m = n
    · subst hmn
      refine ⟨fun j => ?_, fun j => ?_⟩
      · show rhoc I m (V j) (u' j (m + 1)) = u' j m
        rw [u'_new, u'_old j m (by omega)]
        show rhoc I m (V j) (ev j (pu j * (1 + fα j))) = uu j m
        rw [hrho, map_mul, map_add, map_one, hker0 j _ (hfα j), add_zero, mul_one, (hpuv j).1.2]
      · show rhoc I m (V j) (v' j (m + 1)) = v' j m
        rw [v'_new, v'_old j m (by omega)]
        show rhoc I m (V j) (ev j (pv j * (1 + fβ j))) = vv j m
        rw [hrho, map_mul, map_add, map_one, hker0 j _ (hfβ j), add_zero, mul_one, (hpuv j).2.2]
    · have e1 : (fun j => u' j (m + 1)) = fun j => uu j (m + 1) :=
        funext fun j => u'_old j _ (by omega)
      have e2 : (fun j => u' j m) = fun j => uu j m := funext fun j => u'_old j _ (by omega)
      have e3 : (fun j => v' j (m + 1)) = fun j => vv j (m + 1) :=
        funext fun j => v'_old j _ (by omega)
      have e4 : (fun j => v' j m) = fun j => vv j m := funext fun j => v'_old j _ (by omega)
      rw [e1, e2, e3, e4]
      exact hcompu m (by omega)
  · intro m hm
    by_cases hmn : m = n + 1
    · subst hmn
      intro j
      beta_reduce
      rw [u'_new, u'_new, v'_new, v'_new]
      obtain ⟨s1, s2⟩ := hsol j.val j.isLt
      simp only [extN_val] at s1 s2
      have e2 : Θ1 j (ccF j) = rr (n + 1) j := RingEquiv.apply_symm_apply _ _
      have e3 : Θ1 j (ssF j) = resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_right
          (y0 j.succ (n + 1)) *
          resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left (x0 j.castSucc (n + 1)) :=
        RingEquiv.apply_symm_apply _ _
      have A : resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_right (unew j.succ) =
          Θ1 j (uRF j * (1 + evR (n + 1) (ccF j) (ssF j) (b j) (fα j.succ))) := by
        show resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_right
          (ev j.succ (pu j.succ * (1 + fα j.succ))) = _
        rw [← hRu j, map_mul, map_add, map_one]
      have A' : resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_right (vnew j.succ) =
          Θ1 j (vRF j * (1 + evR (n + 1) (ccF j) (ssF j) (b j) (fβ j.succ))) := by
        show resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_right
          (ev j.succ (pv j.succ * (1 + fβ j.succ))) = _
        rw [← hRu j, map_mul, map_add, map_one]
      have B : resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left (unew j.castSucc) =
          Θ1 j (uLF j * (1 + evL (n + 1) (fα j.castSucc))) := by
        show resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left
          (ev j.castSucc (pu j.castSucc * (1 + fα j.castSucc))) = _
        rw [← hLu j, map_mul, map_add, map_one]
      have B' : resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left (vnew j.castSucc) =
          Θ1 j (vLF j * (1 + evL (n + 1) (fβ j.castSucc))) := by
        show resc I (n + 1) _ (V j.castSucc ⊓ V j.succ) inf_le_left
          (ev j.castSucc (pv j.castSucc * (1 + fβ j.castSucc))) = _
        rw [← hLu j, map_mul, map_add, map_one]
      refine ⟨?_, ?_⟩
      · rw [A, B, B']
        calc Θ1 j (uRF j * (1 + evR (n + 1) (ccF j) (ssF j) (b j) (fα j.succ))) *
              rr (n + 1) j
            = Θ1 j (uRF j * (1 + evR (n + 1) (ccF j) (ssF j) (b j) (fα j.succ)) * ccF j) := by
              simp only [map_mul]; rw [e2]
          _ = Θ1 j ((uLF j * (1 + evL (n + 1) (fα j.castSucc))) ^ b j *
                (vLF j * (1 + evL (n + 1) (fβ j.castSucc)))) := congrArg (Θ1 j) s1
          _ = _ := by simp only [map_mul, map_pow]
      · rw [A', B, ← e3]
        calc Θ1 j (ssF j) * Θ1 j (vRF j * (1 + evR (n + 1) (ccF j) (ssF j) (b j) (fβ j.succ))) *
              Θ1 j (uLF j * (1 + evL (n + 1) (fα j.castSucc)))
            = Θ1 j (ssF j * (vRF j * (1 + evR (n + 1) (ccF j) (ssF j) (b j) (fβ j.succ))) *
                (uLF j * (1 + evL (n + 1) (fα j.castSucc)))) := by simp only [map_mul]
          _ = Θ1 j 1 := congrArg (Θ1 j) s2
          _ = 1 := map_one _
    · have e1 : (fun j => u' j m) = fun j => uu j m := funext fun j => u'_old j m hmn
      have e2 : (fun j => v' j m) = fun j => vv j m := funext fun j => v'_old j m hmn
      rw [e1, e2]
      exact heq m (by omega)
  · intro m hm j
    by_cases hmn : m = n + 1
    · subst hmn
      rw [u'_new, v'_new]
      exact ⟨⟨pu j * (1 + fα j), new_sub_one_mem n j _ _ (hpuv j).1.1 (hfα j), rfl⟩,
        ⟨pv j * (1 + fβ j), new_sub_one_mem n j _ _ (hpuv j).2.1 (hfβ j), rfl⟩⟩
    · rw [u'_old j m hmn, v'_old j m hmn]; exact hone m (by omega) j

end Step

section Steps

variable {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (I : X.IdealSheafData)
    {r : ℕ} (V : Fin (r + 1) → X.Opens)

/-- Multiplying the initial coordinates by unit factors solving the multiplicative system gives
good charts. -/
private lemma goodUpTo_of_unitSol (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, I ^ (n + 1) ≤ ZL n) (hZR : ∀ n, I ^ (n + 1) ≤ ZR n) (b : Fin r → ℕ)
    (x0 y0 : ∀ j m, Γ(Sc I m, trc I m (V j)))
    (hpres : ∀ m, PresAt sX I V m (fun j => x0 j m) (fun j => y0 j m))
    (hmark : ∀ m, MarkAt I V ZL ZR hZL hZR m (fun j => x0 j m) (fun j => y0 j m))
    (hov : ∀ m, OvAt I V m (fun j => x0 j m) (fun j => y0 j m))
    (hcomp' : ∀ m, CompatAt I V m (fun j => x0 j (m + 1)) (fun j => x0 j m) ∧
      CompatAt I V m (fun j => y0 j (m + 1)) (fun j => y0 j m))
    (rr : ∀ m, ∀ j : Fin r, Γ(Sc I m, trc I m (V j.castSucc ⊓ V j.succ)))
    (hrat : ∀ m, RatioAt I V b m (fun j => x0 j m) (fun j => y0 j m) (rr m))
    (N : ℕ) (uu vv : ∀ j m, Γ(Sc I m, trc I m (V j)))
    (hsol : UnitSol sX I V b x0 y0 rr N uu vv) :
    GoodUpTo sX I V ZL ZR hZL hZR b N (fun j m => x0 j m * uu j m)
      (fun j m => y0 j m * vv j m) := by
  obtain ⟨hunit, hcomp, heq, hone⟩ := hsol
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · have hU := fun j => (hunit m hm j).1
    have hW := fun j => (hunit m hm j).2
    refine ⟨presAt_mul_isUnit sX I V m _ _ _ _ (hpres m) (fun j => (hone m hm j).1) (fun j =>
        (hone m hm j).2), ?_, ?_, ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hmark m
      refine ⟨?_, ?_⟩
      · simp only
        rw [Ideal.span_singleton_mul_right_unit (hU 0)]; exact h1
      · simp only
        rw [Ideal.span_singleton_mul_right_unit (hW (Fin.last r))]; exact h2
    · intro j
      obtain ⟨h1, h2⟩ := hov m j
      refine ⟨?_, ?_⟩
      · simp only
        rw [Scheme.basicOpen_mul, (Sc I m).basicOpen_of_isUnit (hU _)]
        rw [h1]; exact (inf_eq_left.2 (Scheme.basicOpen_le _ _)).symm
      · simp only
        rw [Scheme.basicOpen_mul, (Sc I m).basicOpen_of_isUnit (hW _)]
        rw [h2]; exact (inf_eq_left.2 (Scheme.basicOpen_le _ _)).symm
    · intro j
      obtain ⟨-, hY⟩ := heq m hm j
      simp only
      rw [map_mul, map_mul]
      linear_combination hY
    · intro j
      obtain ⟨-, hR⟩ := hrat m j
      obtain ⟨hX, -⟩ := heq m hm j
      simp only
      rw [map_mul, map_mul, map_mul, mul_pow, hR]
      linear_combination (resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (x0 j.castSucc m) ^ b j *
        resc I m _ (V j.castSucc ⊓ V j.succ) inf_le_left (y0 j.castSucc m)) * hX
  · obtain ⟨hcu, hcv⟩ := hcomp m hm
    obtain ⟨hx, hy⟩ := hcomp' m
    refine ⟨fun j => ?_, fun j => ?_⟩
    · show rhoc I m _ (x0 j (m + 1) * uu j (m + 1)) = x0 j m * uu j m
      rw [map_mul, hx j, hcu j]
    · show rhoc I m _ (y0 j (m + 1) * vv j (m + 1)) = y0 j m * vv j m
      rw [map_mul, hy j, hcv j]

end Steps

end Proof_lem_mmp_foundation_marked_negative_chain_formal_rigidity

namespace MMP.Mori

open Proof_lem_mmp_foundation_marked_negative_chain_formal_rigidity in
/-- **Formal rigidity of a doubly marked negative chain.** The formal completion of a smooth
surface along a doubly marked chain of smooth rational curves `E₀, …, E_{r-1}` with
`(Eᵢ · Eᵢ) = -bᵢ` and `bᵢ ≥ 2` is the formal plumbing: it has `r + 1` formal coordinate charts
`(x j, y j)`, given level by level on the thickenings `(n+1)E`, with exceptional ideals `(y)`,
`(x y)`, `(x)`, the markings as the axes `x 0 = 0` and `y r = 0`, consecutive charts meeting
exactly where `x j`, equivalently `y (j+1)`, is invertible, non-consecutive charts disjoint, and
on every thickening the monomial transitions `y (j+1) * x j = 1` and
`x (j+1) = x j ^ bⱼ * y j`. -/
@[mmp "lem_mmp_foundation_marked_negative_chain_formal_rigidity"]
public theorem exists_formalPlumbingCharts_of_isSNCChain
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {r : ℕ} (hr : 0 < r) (E : Fin r → PrimeDivisor X) (b : Fin r → ℕ)
    (hb : ∀ i, 2 ≤ b i) (hinj : Function.Injective E)
    (hrat : ∀ i, IsSmoothRationalCurve sX (E i).idealSheaf)
    (hself : ∀ i, IsIntersectionNumber sX (Finsupp.single (E i) 1) (E i).idealSheaf (-(b i : ℤ)))
    (hadj : ∀ i j : Fin r, i.val + 1 = j.val →
      IsIntersectionNumber sX (Finsupp.single (E i) 1) (E j).idealSheaf 1)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → Disjoint (E i).support (E j).support)
    (pL pR : X) (hpLR : pL ≠ pR)
    (hpL : pL ∈ (E ⟨0, hr⟩).support) (hpL' : ∀ i, i ≠ ⟨0, hr⟩ → pL ∉ (E i).support)
    (hpR : pR ∈ (E ⟨r - 1, by omega⟩).support)
    (hpR' : ∀ i, i ≠ ⟨r - 1, by omega⟩ → pR ∉ (E i).support)
    (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZR_succ : ∀ n, ZR n = ZR (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZL_zero : ((ZL 0).support : Set X) = {pL}) (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX) :
    let I := ∏ i, (E i).idealSheaf
    -- the `(n+1)`-st thickening `(n+1)E` and the trace on it of an open of `X`
    let S : ℕ → Scheme.{u} := fun n => (I ^ (n + 1)).subscheme
    let tr : ∀ n, X.Opens → (S n).Opens := fun n V => (I ^ (n + 1)).subschemeι ⁻¹ᵁ V
    -- the constants `K → Γ((n+1)E, U)`
    let σ : ∀ n (U : (S n).Opens), K →+* Γ(S n, U) := fun n U =>
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U le_top).hom
    -- the restriction `(n+2)E → (n+1)E`
    let ρ : ∀ n (V : X.Opens), Γ(S (n + 1), tr (n + 1) V) → Γ(S n, tr n V) := fun n V =>
      ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (tr (n + 1) V) (tr n V)
        (by
          simp only [tr, ← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι, le_refl])).hom
    -- restriction to a smaller open of `X`
    let res : ∀ n (V W : X.Opens), W ≤ V → Γ(S n, tr n V) → Γ(S n, tr n W) :=
      fun n _ _ h => ((S n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom
    -- the exceptional ideal of chart `j`: `(y)`, `(x y)` or `(x)`
    let J : Fin (r + 1) → Ideal (MvPolynomial (Fin 2) K) := fun j =>
      if j = 0 then Ideal.span {MvPolynomial.X 1}
      else if j = Fin.last r then Ideal.span {MvPolynomial.X 0}
      else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    ∃ (V : Fin (r + 1) → X.Opens) (x y : ∀ j n, Γ(S n, tr n (V j))),
      -- the charts cover `E`
      ((I.support : Set X) ⊆ ⋃ j, (V j : Set X)) ∧
      -- `x j`, `y j` are formal functions: compatible along the thickenings
      (∀ j n, ρ n (V j) (x j (n + 1)) = x j n ∧ ρ n (V j) (y j (n + 1)) = y j n) ∧
      -- chart `j` is the completion of `𝔸²` along `J j`
      (∀ j n, IsAffineOpen (tr n (V j)) ∧
        Function.Surjective (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) ∧
        RingHom.ker (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) = J j ^ (n + 1)) ∧
      -- the markings are the axes `x 0 = 0` and `y r = 0`
      (pL ∈ V 0 ∧ pR ∈ V (Fin.last r) ∧
        ∀ n, RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL n)).app (tr n (V 0))).hom =
            Ideal.span {x 0 n} ∧
          RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR n)).app
            (tr n (V (Fin.last r)))).hom = Ideal.span {y (Fin.last r) n}) ∧
      -- consecutive charts meet along the formal neighbourhood of `𝔾_m ⊆ E j`
      (∀ j : Fin r, (((V j.castSucc ⊓ V j.succ : X.Opens) : Set X) ∩ I.support ⊆ (E j).support) ∧
        ∀ n, tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (x j.castSucc n) ∧
          tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (y j.succ n)) ∧
      -- non-consecutive charts do not meet
      (∀ j k : Fin (r + 1), j.val + 2 ≤ k.val →
        ((V j ⊓ V k : X.Opens) : Set X) ∩ I.support = ∅) ∧
      -- the monomial plumbing transitions, on every thickening
      (∀ (j : Fin r) (n : ℕ),
        let W := V j.castSucc ⊓ V j.succ
        res n _ W inf_le_right (y j.succ n) * res n _ W inf_le_left (x j.castSucc n) = 1 ∧
        res n _ W inf_le_right (x j.succ n) =
          res n _ W inf_le_left (x j.castSucc n) ^ b j *
            res n _ W inf_le_left (y j.castSucc n)) := by
  intro I S tr σ ρ res J
  obtain ⟨V, x, y, hcov, hcomp, hpres, ⟨hpL0, hpR0, hmark⟩, hov, hdisj, hinit⟩ :=
    exists_formalCoordinateCharts_of_isSNCChain sX hr E (fun i => (b i : ℤ)) hinj
      hrat hself hadj hfar pL pR hpLR hpL hpL' hpR hpR' ZL ZR hZL hZR hZL_succ hZR_succ hZL_zero
      hZR_zero hZL_curvilinear hZR_curvilinear
  have hpres' : ∀ m, PresAt sX I V m (fun j => x j m) (fun j => y j m) := fun m j => hpres j m
  have hov' : ∀ m, OvAt I V m (fun j => x j m) (fun j => y j m) := fun m j => (hov j).2 m
  have hcomp' : ∀ m, CompatAt I V m (fun j => x j (m + 1)) (fun j => x j m) ∧
      CompatAt I V m (fun j => y j (m + 1)) (fun j => y j m) :=
    fun m => ⟨fun j => (hcomp j m).1, fun j => (hcomp j m).2⟩
  have hY0 : TransYAt I V 0 (fun j => x j 0) (fun j => y j 0) := fun j => (hinit j).1
  have hX1 : TransXAt I V b 1 (fun j => x j 1) (fun j => y j 1) := by
    intro j
    obtain ⟨u, hu1, hu2⟩ := (hinit j).2
    have hpow : ((u ^ ((b j : ℕ) : ℤ) : _ˣ) : Γ(Sc I 1, trc I 1 (V j.castSucc ⊓ V j.succ))) =
        (u : Γ(Sc I 1, trc I 1 (V j.castSucc ⊓ V j.succ))) ^ b j := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hpow, hu1] at hu2
    exact hu2
  obtain ⟨rr, hrat', hrcomp, hr0⟩ := exists_ratio sX I V b x y hpres' hov' hcomp' hX1
  have hbase : ∃ u v : ∀ j m, Γ(Sc I m, trc I m (V j)),
      UnitSol sX I V b x y rr 0 u v := by
    refine ⟨fun _ _ => 1, fun _ _ => 1, ?_, fun m hm => absurd hm (Nat.not_lt_zero _), ?_, ?_⟩
    · intro m _ j; exact ⟨isUnit_one, isUnit_one⟩
    · intro m hm j
      obtain rfl : m = 0 := by omega
      refine ⟨?_, ?_⟩
      · simp only [map_one, one_pow, mul_one, hr0 j]
      · simp only [map_one, mul_one]; exact hY0 j
    · intro m _ j
      exact ⟨⟨1, by simp, by simp⟩, ⟨1, by simp, by simp⟩⟩
  obtain ⟨us, vs, hs⟩ := seq_limit (fun n u v => UnitSol sX I V b x y rr n u v)
    (fun n u v u' v' h hg => by
      obtain ⟨h1, h2, h3, h4⟩ := hg
      have hu : ∀ m, m ≤ n → (fun j => u j m) = fun j => u' j m := fun m hm =>
        funext fun j => (h j m hm).1
      have hv : ∀ m, m ≤ n → (fun j => v j m) = fun j => v' j m := fun m hm =>
        funext fun j => (h j m hm).2
      refine ⟨fun m hm j => ?_, fun m hm => ?_, fun m hm => ?_, fun m hm j => ?_⟩
      · rw [← (h j m hm).1, ← (h j m hm).2]; exact h1 m hm j
      · have e1 : (fun j => u j (m + 1)) = fun j => u' j (m + 1) := hu _ (by omega)
        have e2 : (fun j => v j (m + 1)) = fun j => v' j (m + 1) := hv _ (by omega)
        rw [← e1, ← e2, ← hu m (by omega), ← hv m (by omega)]; exact h2 m hm
      · rw [← hu m hm, ← hv m hm]; exact h3 m hm
      · rw [← (h j m hm).1, ← (h j m hm).2]; exact h4 m hm j)
    hbase
    (fun n u v hg => exists_unitSol_succ sX I V hr b hb x y hpres' hov' hcomp' hY0 rr hrat'
      hrcomp hr0 n u v hg)
  have hall : ∀ n, GoodUpTo sX I V ZL ZR hZL hZR b n (fun j m => x j m * us j m)
      (fun j m => y j m * vs j m) := fun n =>
    goodUpTo_of_unitSol sX I V ZL ZR hZL hZR b x y hpres' hmark hov' hcomp' rr hrat' n us vs (hs n)
  refine ⟨V, fun j m => x j m * us j m, fun j m => y j m * vs j m, hcov, fun j n => ?_,
    fun j n => ?_, ⟨hpL0, hpR0, fun n => ?_⟩, fun j => ?_, hdisj, fun j n => ?_⟩
  · have hc := (hall (n + 1)).2 n (Nat.lt_succ_self n)
    exact ⟨hc.1 j, hc.2 j⟩
  · exact ((hall n).1 n le_rfl).1 j
  · exact ((hall n).1 n le_rfl).2.1
  · exact ⟨(hov j).1, fun n => ((hall n).1 n le_rfl).2.2.1 j⟩
  · exact ⟨((hall n).1 n le_rfl).2.2.2.1 j, ((hall n).1 n le_rfl).2.2.2.2 j⟩

end MMP.Mori

end

