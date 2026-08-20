import LeanProject.Erdos341

set_option linter.style.header false

/-!
# The uniform modulus-`7p` family for Erdős Problem 341

This file formalizes Theorem 5.1 of the accompanying paper.  For every
`p ≥ 18` it defines the paper's seed `A_p` and infinite set `S_p`, proves the
exact greedy recurrence beyond the seed, and proves that the consecutive gaps
in the resulting greedy extension are not eventually periodic.  The separate
elementary cardinality assertion `|A_p| = 7p - 20` is not formalized here.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Erdos3417p

open Erdos341

def M (p : ℕ) : ℕ := 7 * p

def P (p r : ℕ) : Prop :=
  r = p ∨ r = 2 * p ∨ r = 4 * p

def B (p r : ℕ) : Prop :=
  r = M p - 3 ∨ r = M p - 1 ∨ r = 6 * p + 3

def Q (p r : ℕ) : Prop := P p r ∨ B p r

/-- The explicit expansion of
`Q_p ∪ (Q_p - B_p) ∪ (Q_p - P_p)` from the paper. -/
def F (p r : ℕ) : Prop :=
  r = 0 ∨ r = 2 ∨
  r = p - 6 ∨ r = p - 4 ∨ r = p ∨ r = p + 1 ∨ r = p + 3 ∨
  r = 2 * p - 3 ∨ r = 2 * p ∨ r = 2 * p + 1 ∨ r = 2 * p + 3 ∨
  r = 3 * p - 3 ∨ r = 3 * p - 1 ∨ r = 3 * p ∨
  r = 4 * p ∨ r = 4 * p + 1 ∨ r = 4 * p + 3 ∨
  r = 5 * p - 3 ∨ r = 5 * p - 1 ∨ r = 5 * p ∨ r = 5 * p + 3 ∨
  r = 6 * p - 3 ∨ r = 6 * p - 1 ∨ r = 6 * p ∨
  r = 6 * p + 3 ∨ r = 6 * p + 4 ∨ r = 6 * p + 6 ∨
  r = M p - 3 ∨ r = M p - 2 ∨ r = M p - 1

/-- The finite translator set `D_p`, represented in `[0,M)`. -/
def D (p d : ℕ) : Prop :=
  0 < d ∧ d < M p ∧ ¬ F p d

/-- Equality of residues with the only possible carry displayed. -/
def ResidueSum (p a b r : ℕ) : Prop :=
  a + b = r ∨ a + b = M p + r

/-- The definition
`Q_p ∪ (Q_p - B_p) ∪ (Q_p - P_p)`, encoded with representatives in
`[0,M p)`.  The displayed equations are precisely equality modulo `M p`,
with the only possible carry made explicit. -/
def SemanticF (p r : ℕ) : Prop :=
  Q p r ∨
    (∃ q b : ℕ, Q p q ∧ B p b ∧ ResidueSum p r b q) ∨
    (∃ q a : ℕ, Q p q ∧ P p a ∧ ResidueSum p r a q)

/-- The explicit 30-term formula for `F_p` is exactly the
set-theoretic definition. -/
theorem F_iff_semanticF {p r : ℕ} (hp : 18 ≤ p) (hr : r < M p) :
    F p r ↔ SemanticF p r := by
  simp [SemanticF, ResidueSum, Q, P, B, F, M, or_and_right, exists_or] at *
  omega

/-- The infinite set `S_p` in Section 5 of the paper. -/
def S (p n : ℕ) : Prop :=
  D p n ∨ B p (n % M p) ∨
    (n % M p = p ∧ Y0 (n / M p)) ∨
    (n % M p = 2 * p ∧ Y1 (n / M p)) ∨
    (n % M p = 4 * p ∧ Y2 (n / M p))

/-- Membership in the finite seed `A_p` displayed in Theorem 5.1. -/
def Seed (p n : ℕ) : Prop :=
  D p n ∨ B p n ∨
    (∃ b : ℕ, B p b ∧ n = M p + b) ∨
    n = p ∨ n = 4 * p ∨ n = M p + 2 * p ∨ n = M p + 4 * p

noncomputable def seedFinset (p : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * M p)).filter (Seed p)

lemma M_pos {p : ℕ} (hp : 18 ≤ p) : 0 < M p :=
  by simp [M]; omega

lemma M_eq (p : ℕ) : M p = 7 * p := rfl

lemma P_bound {p r : ℕ} (hp : 18 ≤ p) (hr : P p r) : r < M p := by
  simp only [P, M] at *
  omega

lemma B_bound {p r : ℕ} (hp : 18 ≤ p) (hr : B p r) : r < M p := by
  simp only [B, M] at *
  omega

lemma B_positive {p r : ℕ} (hp : 18 ≤ p) (hr : B p r) : 0 < r := by
  simp only [B, M] at *
  omega

lemma D_positive {p d : ℕ} (hd : D p d) : 0 < d := hd.1

lemma D_bound {p d : ℕ} (hd : D p d) : d < M p := hd.2.1

lemma D_not_B {p d : ℕ} (hp : 18 ≤ p) (hd : D p d) : ¬ B p d := by
  intro hb
  simp only [D, B, F, M] at hd hb
  omega

lemma D_not_P {p d : ℕ} (hp : 18 ≤ p) (hd : D p d) : ¬ P p d := by
  intro hP
  simp only [D, P, F, M] at hd hP
  omega

lemma P_disjoint_B {p r : ℕ} (hp : 18 ≤ p) (hP : P p r) (hB : B p r) : False := by
  simp only [P, B, M] at hP hB
  omega

lemma nat_decompose {p n : ℕ} (hp : 18 ≤ p) :
    n = M p * (n / M p) + n % M p := by
  have hm := M_pos hp
  exact (Nat.div_add_mod n (M p)).symm

lemma residue_lt {p n : ℕ} (hp : 18 ≤ p) : n % M p < M p :=
  Nat.mod_lt _ (M_pos hp)

/-- Addition of two representatives has carry zero or one. -/
lemma residueSum_of_add {p a b n : ℕ} (hp : 18 ≤ p) (hab : a + b = n) :
    ResidueSum p (a % M p) (b % M p) (n % M p) := by
  have hm := M_pos hp
  have ha := Nat.mod_lt a hm
  have hb := Nat.mod_lt b hm
  have hn := Nat.mod_lt n hm
  have hmod : (a % M p + b % M p) % M p = n % M p := by
    rw [← Nat.add_mod, hab]
  simp only [ResidueSum]
  by_cases hlt : a % M p + b % M p < M p
  · left
    have := Nat.mod_eq_of_lt hlt
    omega
  · right
    have hge : M p ≤ a % M p + b % M p := Nat.le_of_not_gt hlt
    have hsum : a % M p + b % M p < 2 * M p := by omega
    have hrewrite :
        (a % M p + b % M p) % M p =
          a % M p + b % M p - M p := by
      rw [Nat.mod_eq_sub_mod hge]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hrewrite] at hmod
    omega

lemma selected_positive {p n : ℕ} (hp : 18 ≤ p) (hn : S p n) : 0 < n := by
  rcases hn with hnD | hnB | hnP | hnP | hnP
  · exact D_positive hnD
  · have hr := B_positive hp hnB
    have hm := Nat.mod_le n (M p)
    omega
  · have : 0 < p := by omega
    have hmod := Nat.mod_le n (M p)
    omega
  · have hmod := Nat.mod_le n (M p)
    omega
  · have hmod := Nat.mod_le n (M p)
    omega

lemma selected_background (p q b : ℕ) (hp : 18 ≤ p) (hb : B p b) :
    S p (M p * q + b) := by
  have hb0 := B_bound hp hb
  right
  left
  simpa [S, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hb0] using hb

lemma selected_y0 (p q : ℕ) (hp : 18 ≤ p) (hq : Y0 q) :
    S p (M p * q + p) := by
  have hpM : p < M p := by simp [M]; omega
  right
  right
  left
  constructor
  · simp [Nat.add_mod, Nat.mod_eq_of_lt hpM]
  · have hdiv : (M p * q + p) / M p = q := by
      rw [Nat.mul_comm (M p) q]
      exact Nat.div_eq_of_lt_le (by omega)
        (by simpa [Nat.succ_mul] using Nat.add_lt_add_left hpM (q * M p))
    simpa [hdiv] using hq

lemma selected_y1 (p q : ℕ) (hp : 18 ≤ p) (hq : Y1 q) :
    S p (M p * q + 2 * p) := by
  have hpM : 2 * p < M p := by simp [M]; omega
  right
  right
  right
  left
  constructor
  · simp [Nat.add_mod, Nat.mod_eq_of_lt hpM]
  · have hdiv : (M p * q + 2 * p) / M p = q := by
      rw [Nat.mul_comm (M p) q]
      exact Nat.div_eq_of_lt_le (by omega)
        (by simpa [Nat.succ_mul] using Nat.add_lt_add_left hpM (q * M p))
    simpa [hdiv] using hq

lemma selected_y2 (p q : ℕ) (hp : 18 ≤ p) (hq : Y2 q) :
    S p (M p * q + 4 * p) := by
  have hpM : 4 * p < M p := by simp [M]; omega
  right
  right
  right
  right
  constructor
  · simp [Nat.add_mod, Nat.mod_eq_of_lt hpM]
  · have hdiv : (M p * q + 4 * p) / M p = q := by
      rw [Nat.mul_comm (M p) q]
      exact Nat.div_eq_of_lt_le (by omega)
        (by simpa [Nat.succ_mul] using Nat.add_lt_add_left hpM (q * M p))
    simpa [hdiv] using hq

lemma selected_coarse {p n : ℕ} (hn : S p n) :
    D p n ∨ B p (n % M p) ∨ P p (n % M p) := by
  rcases hn with hnD | hnB | hn0 | hn1 | hn2
  · exact Or.inl hnD
  · exact Or.inr (Or.inl hnB)
  · exact Or.inr (Or.inr (Or.inl hn0.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hn1.1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hn2.1)))

lemma selected_at_p {p n : ℕ} (hp : 18 ≤ p) (hS : S p n)
    (hr : n % M p = p) : Y0 (n / M p) := by
  rcases hS with hD | hB | h0 | h1 | h2
  · have hdP : P p n := Or.inl (by
      have hbound := D_bound hD
      have hmod : n % M p = n := Nat.mod_eq_of_lt hbound
      omega)
    exact (D_not_P hp hD hdP).elim
  · exact (P_disjoint_B hp (Or.inl hr) hB).elim
  · exact h0.2
  · omega
  · omega

lemma selected_at_2p {p n : ℕ} (hp : 18 ≤ p) (hS : S p n)
    (hr : n % M p = 2 * p) : Y1 (n / M p) := by
  rcases hS with hD | hB | h0 | h1 | h2
  · have hdP : P p n := Or.inr (Or.inl (by
      have hbound := D_bound hD
      have hmod : n % M p = n := Nat.mod_eq_of_lt hbound
      omega))
    exact (D_not_P hp hD hdP).elim
  · exact (P_disjoint_B hp (Or.inr (Or.inl hr)) hB).elim
  · omega
  · exact h1.2
  · omega

lemma selected_at_4p {p n : ℕ} (hp : 18 ≤ p) (hS : S p n)
    (hr : n % M p = 4 * p) : Y2 (n / M p) := by
  rcases hS with hD | hB | h0 | h1 | h2
  · have hdP : P p n := Or.inr (Or.inr (by
      have hbound := D_bound hD
      have hmod : n % M p = n := Nat.mod_eq_of_lt hbound
      omega))
    exact (D_not_P hp hD hdP).elim
  · exact (P_disjoint_B hp (Or.inr (Or.inr hr)) hB).elim
  · omega
  · omega
  · exact h2.2

/-! ## The uniform finite shield -/

/-- The five exceptional first summands in the covering argument really lie
in `D_p`; this is one of the two memberships left implicit in the paper. -/
lemma exceptional_D (p : ℕ) (hp : 18 ≤ p) :
    D p (2 * p - 10) ∧ D p (4 * p - 7) ∧ D p (6 * p - 7) ∧
      D p (M p - 7) ∧ D p (p - 7) := by
  simp only [D, F, M]
  omega

lemma cover_classification
    (p r : ℕ) (hp : 18 ≤ p) (_hr0 : r < M p) (hr : ¬ Q p r)
    (hf : F p (r + 1)) :
    r = p - 7 ∨ r = 3 * p - 4 ∨ r = 5 * p - 4 ∨
      r = 6 * p - 4 ∨ r = M p - 4 ∨ r = M p - 2 ∨
      ¬ F p (r + 3) := by
  simp only [Q, P, B, F, M] at *
  omega

/-- Every residue outside the selected rails is covered by `D_p+B_p`. -/
theorem residue_cover
    (p r : ℕ) (hp : 18 ≤ p) (hr0 : r < M p) (hr : ¬ Q p r) :
    ∃ d b : ℕ, D p d ∧ B p b ∧ ResidueSum p d b r := by
  have hrne : r ≠ M p - 1 := by
    intro hre
    apply hr
    right
    exact Or.inr (Or.inl hre)
  have hrne3 : r ≠ M p - 3 := by
    intro hre
    apply hr
    right
    exact Or.inl hre
  by_cases hrne2 : r = M p - 2
  · refine ⟨1, M p - 3, ?_, Or.inl rfl, ?_⟩
    · simp only [D, F, M]
      omega
    · left
      simp only [M] at hrne2 ⊢
      omega
  have hf_lt : r + 1 < M p := by omega
  by_cases hf : F p (r + 1)
  · rcases cover_classification p r hp hr0 hr hf with
      h | h | h | h | h | h | hnotF
    · rcases exceptional_D p hp with ⟨hd, _, _, _, _⟩
      refine ⟨2 * p - 10, 6 * p + 3, hd, Or.inr (Or.inr rfl), ?_⟩
      right
      simp only [M] at h ⊢
      omega
    · rcases exceptional_D p hp with ⟨_, hd, _, _, _⟩
      refine ⟨4 * p - 7, 6 * p + 3, hd, Or.inr (Or.inr rfl), ?_⟩
      right
      simp only [M] at h ⊢
      omega
    · rcases exceptional_D p hp with ⟨_, _, hd, _, _⟩
      refine ⟨6 * p - 7, 6 * p + 3, hd, Or.inr (Or.inr rfl), ?_⟩
      right
      simp only [M] at h ⊢
      omega
    · rcases exceptional_D p hp with ⟨_, _, _, hd, _⟩
      refine ⟨M p - 7, 6 * p + 3, hd, Or.inr (Or.inr rfl), ?_⟩
      right
      simp only [M] at h ⊢
      omega
    · rcases exceptional_D p hp with ⟨_, _, _, _, hd⟩
      refine ⟨p - 7, 6 * p + 3, hd, Or.inr (Or.inr rfl), ?_⟩
      left
      simp only [M] at h ⊢
      omega
    · exact (hrne2 h).elim
    · refine ⟨r + 3, M p - 3, ?_, Or.inl rfl, ?_⟩
      · refine ⟨by omega, ?_, hnotF⟩
        simp only [M] at hr0 hrne hrne2 hrne3 ⊢
        omega
      · right
        simp only [M] at hr0 hrne hrne2 hrne3 ⊢
        omega
  · refine ⟨r + 1, M p - 1, ?_, ?_, ?_⟩
    · exact ⟨by omega, hf_lt, hf⟩
    · exact Or.inr (Or.inl rfl)
    · right
      simp only [M] at hr0 hrne hrne2 hrne3 ⊢
      omega

theorem avoid_DB
    (p d b r : ℕ) (hp : 18 ≤ p) (hd : D p d) (hb : B p b)
    (hr0 : r < M p) (hs : ResidueSum p d b r) :
    ¬ Q p r := by
  simp only [Q, P, B, D, F, ResidueSum, M] at *
  omega

theorem avoid_DP
    (p d a r : ℕ) (hp : 18 ≤ p) (hd : D p d) (ha : P p a)
    (hr0 : r < M p) (hs : ResidueSum p d a r) :
    ¬ Q p r := by
  simp only [Q, P, B, D, F, ResidueSum, M] at *
  omega

theorem avoid_BB
    (p a b r : ℕ) (hp : 18 ≤ p) (ha : B p a) (hb : B p b)
    (_hr0 : r < M p) (hs : ResidueSum p a b r) :
    ¬ Q p r := by
  simp only [Q, P, B, ResidueSum, M] at *
  omega

theorem avoid_PB
    (p a b r : ℕ) (hp : 18 ≤ p) (ha : P p a) (hb : B p b)
    (_hr0 : r < M p) (hs : ResidueSum p a b r) :
    ¬ Q p r := by
  simp only [Q, P, B, ResidueSum, M] at *
  omega

set_option maxHeartbeats 8000000 in
-- The uniform symbolic analysis of all controller-residue cases needs a larger heartbeat limit.
/-- Only the three diagonal controller pairs return to `Q_p`. -/
theorem controller_diagonals
    (p a b r : ℕ) (hp : 18 ≤ p) (ha : P p a) (hb : P p b)
    (hr : Q p r) (hr0 : r < M p) (hs : ResidueSum p a b r) :
    (a = p ∧ b = p ∧ r = 2 * p ∧ a + b = r) ∨
    (a = 2 * p ∧ b = 2 * p ∧ r = 4 * p ∧ a + b = r) ∨
    (a = 4 * p ∧ b = 4 * p ∧ r = p ∧ a + b = M p + r) := by
  simp only [P, B, Q, ResidueSum, M] at *
  omega

/-! ## The exact recurrence -/

lemma selected_residue_of_large {p n : ℕ} (_hp : 18 ≤ p)
    (hn : 2 * M p - 1 < n) (hS : S p n) : Q p (n % M p) := by
  rcases selected_coarse hS with hD | hB | hP
  · have hd := D_bound hD
    omega
  · exact Or.inr hB
  · exact Or.inl hP

lemma residueSum_comm {p a b r : ℕ} (h : ResidueSum p a b r) :
    ResidueSum p b a r := by
  rcases h with h | h
  · left; omega
  · right; omega

theorem selected_not_pairSum
    {p n : ℕ} (hp : 18 ≤ p) (hn : 2 * M p - 1 < n) (hS : S p n) :
    ¬ PairSum (S p) n := by
  intro hsum
  rcases hsum with ⟨a, b, haS, hbS, hab⟩
  have haPos := selected_positive hp haS
  have hbPos := selected_positive hp hbS
  have htQ := selected_residue_of_large hp hn hS
  have hrs := residueSum_of_add hp hab
  rcases selected_coarse haS with haD | haB | haP
  · rcases selected_coarse hbS with hbD | hbB | hbP
    · have haBound := D_bound haD
      have hbBound := D_bound hbD
      omega
    · have haMod : a % M p = a := Nat.mod_eq_of_lt (D_bound haD)
      have hrs' : ResidueSum p a (b % M p) (n % M p) := by
        simpa [haMod] using hrs
      exact (avoid_DB p a (b % M p) (n % M p) hp haD hbB
        (residue_lt hp) hrs') htQ
    · have haMod : a % M p = a := Nat.mod_eq_of_lt (D_bound haD)
      have hrs' : ResidueSum p a (b % M p) (n % M p) := by
        simpa [haMod] using hrs
      exact (avoid_DP p a (b % M p) (n % M p) hp haD hbP
        (residue_lt hp) hrs') htQ
  · rcases selected_coarse hbS with hbD | hbB | hbP
    · have hbMod : b % M p = b := Nat.mod_eq_of_lt (D_bound hbD)
      have hrs' : ResidueSum p b (a % M p) (n % M p) := by
        simpa [hbMod] using residueSum_comm hrs
      exact (avoid_DB p b (a % M p) (n % M p) hp hbD haB
        (residue_lt hp) hrs') htQ
    · exact (avoid_BB p (a % M p) (b % M p) (n % M p) hp haB hbB
        (residue_lt hp) hrs) htQ
    · exact (avoid_PB p (b % M p) (a % M p) (n % M p) hp hbP haB
        (residue_lt hp) (residueSum_comm hrs)) htQ
  · rcases selected_coarse hbS with hbD | hbB | hbP
    · have hbMod : b % M p = b := Nat.mod_eq_of_lt (D_bound hbD)
      have hrs' : ResidueSum p b (a % M p) (n % M p) := by
        simpa [hbMod] using residueSum_comm hrs
      exact (avoid_DP p b (a % M p) (n % M p) hp hbD haP
        (residue_lt hp) hrs') htQ
    · exact (avoid_PB p (a % M p) (b % M p) (n % M p) hp haP hbB
        (residue_lt hp) hrs) htQ
    · rcases controller_diagonals p (a % M p) (b % M p) (n % M p)
        hp haP hbP htQ (residue_lt hp) hrs with h0 | h1 | h2
      · rcases h0 with ⟨ha, hb, hnres, _⟩
        have hya := selected_at_p hp haS ha
        have hyb := selected_at_p hp hbS hb
        have hyn := selected_at_2p hp hS hnres
        have haDec := nat_decompose (p := p) (n := a) hp
        have hbDec := nat_decompose (p := p) (n := b) hp
        have hnDec := nat_decompose (p := p) (n := n) hp
        have hmul :
            M p * (a / M p + b / M p) = M p * (n / M p) := by
          simp only [Nat.mul_add]
          omega
        have hq : a / M p + b / M p = n / M p :=
          Nat.eq_of_mul_eq_mul_left (M_pos hp) hmul
        exact ((controller_01 (n / M p)).mp hyn)
          ⟨a / M p, b / M p, hya, hyb, hq⟩
      · rcases h1 with ⟨ha, hb, hnres, _⟩
        have hya := selected_at_2p hp haS ha
        have hyb := selected_at_2p hp hbS hb
        have hyn := selected_at_4p hp hS hnres
        have haDec := nat_decompose (p := p) (n := a) hp
        have hbDec := nat_decompose (p := p) (n := b) hp
        have hnDec := nat_decompose (p := p) (n := n) hp
        have hmul :
            M p * (a / M p + b / M p) = M p * (n / M p) := by
          simp only [Nat.mul_add]
          omega
        have hq : a / M p + b / M p = n / M p :=
          Nat.eq_of_mul_eq_mul_left (M_pos hp) hmul
        exact ((controller_12 (n / M p)).mp hyn)
          ⟨a / M p, b / M p, hya, hyb, hq⟩
      · rcases h2 with ⟨ha, hb, hnres, _⟩
        have hya := selected_at_4p hp haS ha
        have hyb := selected_at_4p hp hbS hb
        have hyn := selected_at_p hp hS hnres
        have haDec := nat_decompose (p := p) (n := a) hp
        have hbDec := nat_decompose (p := p) (n := b) hp
        have hnDec := nat_decompose (p := p) (n := n) hp
        have hmul :
            M p * (a / M p + b / M p + 1) = M p * (n / M p) := by
          have hM : M p = 7 * p := rfl
          simp only [Nat.mul_add]
          omega
        have hq : a / M p + b / M p + 1 = n / M p :=
          Nat.eq_of_mul_eq_mul_left (M_pos hp) hmul
        have hpair : PairSum Y2 (a / M p + b / M p) :=
          ⟨a / M p, b / M p, hya, hyb, rfl⟩
        have hyshift : Y0 (a / M p + b / M p + 1) := by
          convert hyn using 1
        exact ((controller_20 (a / M p + b / M p)).mp hyshift) hpair

lemma quotient_ge_two {p n : ℕ} (hp : 18 ≤ p) (hn : 2 * M p - 1 < n) :
    2 ≤ n / M p := by
  apply (Nat.le_div_iff_mul_le (M_pos hp)).2
  omega

theorem garbage_covered
    {p n : ℕ} (hp : 18 ≤ p) (hn : 2 * M p - 1 < n)
    (hQ : ¬ Q p (n % M p)) : PairSum (S p) n := by
  rcases residue_cover p (n % M p) hp (residue_lt hp) hQ with
    ⟨d, b, hd, hb, hsum⟩
  have hnDec := nat_decompose (p := p) (n := n) hp
  have hq := quotient_ge_two hp hn
  rcases hsum with hsum | hsum
  · refine ⟨d, M p * (n / M p) + b, Or.inl hd,
      selected_background p (n / M p) b hp hb, ?_⟩
    omega
  · refine ⟨d, M p * (n / M p - 1) + b, Or.inl hd,
      selected_background p (n / M p - 1) b hp hb, ?_⟩
    have hqsplit : n / M p = (n / M p - 1) + 1 := by omega
    rw [hqsplit] at hnDec
    simp only [Nat.mul_add, Nat.mul_one] at hnDec
    omega

theorem omitted_controller_covered
    {p n : ℕ} (hp : 18 ≤ p) (hn : 2 * M p - 1 < n)
    (hP : P p (n % M p)) (hnot : ¬ S p n) : PairSum (S p) n := by
  have hq := quotient_ge_two hp hn
  rcases hP with hr | hr | hr
  · have hny0 : ¬ Y0 (n / M p) := by
      intro hy
      exact hnot (Or.inr (Or.inr (Or.inl ⟨hr, hy⟩)))
    have hpair : PairSum Y2 (n / M p - 1) := by
      by_contra hno
      apply hny0
      have hg := (controller_20 (n / M p - 1)).mpr hno
      convert hg using 1; omega
    rcases hpair with ⟨a, b, ha, hb, hab⟩
    have hnDec := nat_decompose (p := p) (n := n) hp
    refine ⟨M p * a + 4 * p, M p * b + 4 * p,
      selected_y2 p a hp ha, selected_y2 p b hp hb, ?_⟩
    have hM : M p = 7 * p := rfl
    have hqsplit : n / M p = (n / M p - 1) + 1 := by omega
    rw [hr, hqsplit, ← hab] at hnDec
    simp only [Nat.mul_add, Nat.mul_one] at hnDec
    omega
  · have hny1 : ¬ Y1 (n / M p) := by
      intro hy
      exact hnot (Or.inr (Or.inr (Or.inr (Or.inl ⟨hr, hy⟩))))
    have hpair : PairSum Y0 (n / M p) := by
      by_contra hno
      exact hny1 ((controller_01 (n / M p)).mpr hno)
    rcases hpair with ⟨a, b, ha, hb, hab⟩
    have hnDec := nat_decompose (p := p) (n := n) hp
    refine ⟨M p * a + p, M p * b + p,
      selected_y0 p a hp ha, selected_y0 p b hp hb, ?_⟩
    rw [hr, ← hab] at hnDec
    simp only [Nat.mul_add] at hnDec
    omega
  · have hny2 : ¬ Y2 (n / M p) := by
      intro hy
      exact hnot (Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, hy⟩))))
    have hpair : PairSum Y1 (n / M p) := by
      by_contra hno
      exact hny2 ((controller_12 (n / M p)).mpr hno)
    rcases hpair with ⟨a, b, ha, hb, hab⟩
    have hnDec := nat_decompose (p := p) (n := n) hp
    refine ⟨M p * a + 2 * p, M p * b + 2 * p,
      selected_y1 p a hp ha, selected_y1 p b hp hb, ?_⟩
    rw [hr, ← hab] at hnDec
    simp only [Nat.mul_add] at hnDec
    omega

theorem omitted_pairSum
    {p n : ℕ} (hp : 18 ≤ p) (hn : 2 * M p - 1 < n)
    (hnot : ¬ S p n) : PairSum (S p) n := by
  by_cases hB : B p (n % M p)
  · exact (hnot (Or.inr (Or.inl hB))).elim
  by_cases hP : P p (n % M p)
  · exact omitted_controller_covered hp hn hP hnot
  · exact garbage_covered hp hn (by simp [Q, hP, hB])

/-- The exact recurrence in Theorem 5.3 of the paper. -/
theorem exact_recurrence (p : ℕ) (hp : 18 ≤ p) :
    ∀ n : ℕ, 2 * M p - 1 < n →
      (S p n ↔ ¬ PairSum (S p) n) := by
  intro n hn
  constructor
  · exact selected_not_pairSum hp hn
  · intro hnotSum
    by_contra hnotSelected
    exact hnotSum (omitted_pairSum hp hn hnotSelected)

/-! ## The prescribed seed -/

lemma quotient_le_one {p n : ℕ} (hp : 18 ≤ p) (hn : n ≤ 2 * M p - 1) :
    n / M p ≤ 1 := by
  by_contra h
  have htwo : 2 ≤ n / M p := by omega
  have hmul : 2 * M p ≤ n :=
    (Nat.le_div_iff_mul_le (M_pos hp)).mp htwo
  have hsub : 2 * M p - 1 < 2 * M p := by
    have hm := M_pos hp
    omega
  exact (Nat.not_le_of_lt (lt_of_le_of_lt hn hsub)) hmul

/-- The formula for `S_p` has exactly the seed prefix stated in the paper. -/
theorem seed_prefix (p : ℕ) (hp : 18 ≤ p) :
    ∀ n : ℕ, n ≤ 2 * M p - 1 → (S p n ↔ Seed p n) := by
  intro n hn
  have hqle := quotient_le_one hp hn
  have hq : n / M p = 0 ∨ n / M p = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp hqle
  constructor
  · intro hS
    rcases hS with hD | hB | h0 | h1 | h2
    · exact Or.inl hD
    · have hnDec := nat_decompose (p := p) (n := n) hp
      rcases hq with hq | hq
      · right; left
        have hnEq : n = n % M p := by
          rw [hnDec, hq]
          simp
        rw [hnEq]
        exact hB
      · right; right; left
        refine ⟨n % M p, hB, ?_⟩
        rw [hnDec, hq]
        simp
    · rcases hq with hq | hq
      · right; right; right; left
        have hnDec := nat_decompose (p := p) (n := n) hp
        rw [hnDec, hq, h0.1]
        simp
      · exact (not_y0_one (by simpa [hq] using h0.2)).elim
    · rcases hq with hq | hq
      · exact (not_y1_zero (by simpa [hq] using h1.2)).elim
      · right; right; right; right; right; left
        have hnDec := nat_decompose (p := p) (n := n) hp
        rw [hnDec, hq, h1.1]
        simp
    · rcases hq with hq | hq
      · right; right; right; right; left
        have hnDec := nat_decompose (p := p) (n := n) hp
        rw [hnDec, hq, h2.1]
        simp
      · right; right; right; right; right; right
        have hnDec := nat_decompose (p := p) (n := n) hp
        rw [hnDec, hq, h2.1]
        simp
  · intro hSeed
    rcases hSeed with hD | hB | hMB | hp0 | h4p | hM2p | hM4p
    · exact Or.inl hD
    · simpa using selected_background p 0 n hp hB
    · rcases hMB with ⟨b, hb, rfl⟩
      simpa [Nat.add_comm] using selected_background p 1 b hp hb
    · subst n
      simpa using selected_y0 p 0 hp y0_zero
    · subst n
      simpa using selected_y2 p 0 hp y2_zero
    · subst n
      simpa [Nat.add_comm] using selected_y1 p 1 hp y1_one
    · subst n
      simpa [Nat.add_comm] using selected_y2 p 1 hp y2_one

lemma Seed_bound {p n : ℕ} (hp : 18 ≤ p) (hn : Seed p n) :
    n < 2 * M p := by
  rcases hn with hD | hB | hMB | hp0 | h4p | hM2p | hM4p
  · have := D_bound hD; omega
  · have := B_bound hp hB; omega
  · rcases hMB with ⟨b, hb, rfl⟩
    have := B_bound hp hb; omega
  · simp only [M] at *; omega
  · simp only [M] at *; omega
  · simp only [M] at *; omega
  · simp only [M] at *; omega

lemma mem_seedFinset_iff {p n : ℕ} (hp : 18 ≤ p) :
    n ∈ seedFinset p ↔ Seed p n := by
  classical
  simp only [seedFinset, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨Seed_bound hp h, h⟩

/-! ## Greedy enumeration and nonperiodicity -/

theorem S_is_greedy (p : ℕ) (hp : 18 ≤ p) :
    GreedyExtension (Seed p) (S p) (2 * M p - 1) := by
  exact ⟨seed_prefix p hp, exact_recurrence p hp⟩

lemma background_rail_mem (p q : ℕ) (hp : 18 ≤ p) :
    S p (M p * q + (M p - 1)) := by
  apply selected_background p q (M p - 1) hp
  exact Or.inr (Or.inl rfl)

theorem S_infinite (p : ℕ) (hp : 18 ≤ p) :
    {n : ℕ | S p n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun q : ℕ ↦ M p * q + (M p - 1))
  · intro q r h
    have hm := M_pos hp
    dsimp at h
    have hmul : M p * q = M p * r := Nat.add_right_cancel h
    exact Nat.eq_of_mul_eq_mul_left hm hmul
  · intro q
    exact background_rail_mem p q hp

noncomputable def enumeration (p n : ℕ) : ℕ := enumOf (S p) n

noncomputable def gap (p n : ℕ) : ℕ := gapOf (S p) n

theorem enumeration_strictMono (p : ℕ) (hp : 18 ≤ p) :
    StrictMono (enumeration p) := by
  exact Nat.nth_strictMono (S_infinite p hp)

theorem enumeration_range (p : ℕ) (hp : 18 ≤ p) :
    Set.range (enumeration p) = {n : ℕ | S p n} := by
  exact Nat.range_nth_of_infinite (S_infinite p hp)

theorem enumeration_least_greedy_step (p i : ℕ) (hp : 18 ≤ p)
    (hi : 2 * M p - 1 ≤ enumeration p i) :
    LeastGreedyStep (enumeration p) i := by
  have hstrict := enumeration_strictMono p hp
  have hnext : enumeration p i < enumeration p (i + 1) :=
    hstrict (by omega)
  refine ⟨hnext, ?_, ?_⟩
  · intro hprefix
    rcases hprefix with ⟨j, hj, k, hk, hsum⟩
    have hSj : S p (enumeration p j) := by
      simpa [enumeration, enumOf] using
        Nat.nth_mem_of_infinite (S_infinite p hp) j
    have hSk : S p (enumeration p k) := by
      simpa [enumeration, enumOf] using
        Nat.nth_mem_of_infinite (S_infinite p hp) k
    have hSnext : S p (enumeration p (i + 1)) := by
      simpa [enumeration, enumOf] using
        Nat.nth_mem_of_infinite (S_infinite p hp) (i + 1)
    have hpair : PairSum (S p) (enumeration p (i + 1)) :=
      ⟨enumeration p j, enumeration p k, hSj, hSk, hsum⟩
    exact ((exact_recurrence p hp _ (by omega)).mp hSnext) hpair
  · intro t hit hti
    have hnotS : ¬ S p t := by
      intro hSt
      have htRange : t ∈ Set.range (enumeration p) := by
        rw [enumeration_range p hp]
        exact hSt
      rcases htRange with ⟨j, hj⟩
      have hij : i < j := by
        apply (hstrict.lt_iff_lt).mp
        simpa [hj] using hit
      have hji : j < i + 1 := by
        apply (hstrict.lt_iff_lt).mp
        simpa [hj] using hti
      omega
    have hpair : PairSum (S p) t := by
      by_contra hnotPair
      exact hnotS ((exact_recurrence p hp t (by omega)).mpr hnotPair)
    rcases hpair with ⟨u, v, huS, hvS, huv⟩
    have huPos := selected_positive hp huS
    have hvPos := selected_positive hp hvS
    have huRange : u ∈ Set.range (enumeration p) := by
      rw [enumeration_range p hp]
      exact huS
    have hvRange : v ∈ Set.range (enumeration p) := by
      rw [enumeration_range p hp]
      exact hvS
    rcases huRange with ⟨j, hj⟩
    rcases hvRange with ⟨k, hk⟩
    have hju : j ≤ i := by
      have : enumeration p j < enumeration p (i + 1) := by
        rw [hj]
        omega
      exact Nat.lt_succ_iff.mp ((hstrict.lt_iff_lt).mp this)
    have hkv : k ≤ i := by
      have : enumeration p k < enumeration p (i + 1) := by
        rw [hk]
        omega
      exact Nat.lt_succ_iff.mp ((hstrict.lt_iff_lt).mp this)
    exact ⟨j, hju, k, hkv, by simpa [hj, hk] using huv⟩

theorem enumeration_hits_seed_max (p : ℕ) (hp : 18 ≤ p) :
    ∃ i : ℕ, enumeration p i = 2 * M p - 1 := by
  have hb : B p (M p - 1) := Or.inr (Or.inl rfl)
  have hSeed : Seed p (2 * M p - 1) := by
    right
    right
    left
    refine ⟨M p - 1, hb, ?_⟩
    have hm := M_pos hp
    omega
  have hS : S p (2 * M p - 1) :=
    (seed_prefix p hp _ (by omega)).mpr hSeed
  have : 2 * M p - 1 ∈ Set.range (enumeration p) := by
    rw [enumeration_range p hp]
    exact hS
  simpa using this

theorem least_next_rule_after_seed (p : ℕ) (hp : 18 ≤ p) :
    ∃ i : ℕ, enumeration p i = 2 * M p - 1 ∧
      ∀ j : ℕ, i ≤ j → LeastGreedyStep (enumeration p) j := by
  rcases enumeration_hits_seed_max p hp with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  intro j hij
  apply enumeration_least_greedy_step p j hp
  have hmono := (enumeration_strictMono p hp).monotone hij
  simpa [hi] using hmono

lemma S_rail_p (p q : ℕ) (hp : 18 ≤ p) :
    S p (M p * q + p) ↔ Y0 q := by
  have hpM : p < M p := by simp [M]; omega
  have hmod : (M p * q + p) % M p = p := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hpM]
  have hdiv : (M p * q + p) / M p = q := by
    rw [Nat.mul_comm (M p) q]
    exact Nat.div_eq_of_lt_le (by omega)
      (by simpa [Nat.succ_mul] using Nat.add_lt_add_left hpM (q * M p))
  have hD : ¬ D p (M p * q + p) := by
    intro hd
    by_cases hq0 : q = 0
    · subst q
      exact D_not_P hp hd (by simp [P])
    · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
      have hle : M p ≤ M p * q := by
        simpa using Nat.mul_le_mul_left (M p) hq1
      have hbound := D_bound hd
      omega
  have hB : ¬ B p p := by simp only [B, M]; omega
  have hp2 : p ≠ 2 * p := by omega
  have hp4 : p ≠ 4 * p := by omega
  simp [S, hD, hmod, hdiv, hB, hp2, hp4]

theorem not_eventuallyPeriodic_S (p : ℕ) (hp : 18 ≤ p) :
    ¬ EventuallyPeriodic (S p) := by
  intro hS
  apply not_eventuallyPeriodic_Y0
  rcases hS with ⟨N, h, hh, hperiod⟩
  refine ⟨N, h, hh, ?_⟩
  intro q hq
  rw [← S_rail_p p (q + h) hp, ← S_rail_p p q hp]
  have hm1 : 1 ≤ M p := M_pos hp
  have hqmul : q ≤ M p * q := by
    simpa using Nat.mul_le_mul_right q hm1
  have hbase : N ≤ M p * q + p := by omega
  have hiter := iterate_eventual_period hperiod (M p) (M p * q + p) hbase
  have harg : M p * (q + h) + p = (M p * q + p) + M p * h := by
    rw [Nat.mul_add]
    omega
  rw [harg]
  exact hiter

theorem gap_not_eventuallyPeriodic (p : ℕ) (hp : 18 ≤ p) :
    ¬ EventuallyPeriodic (gap p) := by
  intro hg
  exact not_eventuallyPeriodic_S p hp
    (eventual_gap_periodicity_implies_membership_periodicity
      (S p) (S_infinite p hp) hg)

theorem quantified_gap_nonperiodicity (p : ℕ) (hp : 18 ≤ p) :
    ∀ K : ℕ, 1 ≤ K → ∀ h : ℕ, 1 ≤ h →
      ∃ m : ℕ, K ≤ m ∧ gap p (m + h) ≠ gap p m := by
  intro K hK h hh
  by_contra hcontra
  apply gap_not_eventuallyPeriodic p hp
  refine ⟨K, h, hh, ?_⟩
  intro m hm
  by_contra hne
  exact hcontra ⟨m, hm, hne⟩

/-- The nonperiodicity assertion of Theorem 5.1 -/
theorem theorem_5_1_nonperiodicity :
    ∀ p : ℕ, 18 ≤ p →
      GreedyExtension (Seed p) (S p) (2 * M p - 1) ∧
      (∃ i : ℕ, enumeration p i = 2 * M p - 1 ∧
        ∀ j : ℕ, i ≤ j → LeastGreedyStep (enumeration p) j) ∧
      (∀ K : ℕ, 1 ≤ K → ∀ h : ℕ, 1 ≤ h →
        ∃ m : ℕ, K ≤ m ∧ gap p (m + h) ≠ gap p m) := by
  intro p hp
  exact ⟨S_is_greedy p hp, least_next_rule_after_seed p hp,
    quantified_gap_nonperiodicity p hp⟩

#print axioms theorem_5_1_nonperiodicity

end Erdos3417p
