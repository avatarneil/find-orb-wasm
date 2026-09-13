import IEEEBounds

/- GPL-2.0-or-later. Bijective finite binary64 field/64-bit-word encoding. -/
namespace FindOrbRounding
noncomputable section

def bits64 (v : Encoding 52 2044) : ℕ :=
  (if v.1 then 2^63 else 0) + v.2.1.val * 2^52 + v.2.2.val

theorem bits64_bounded (v : Encoding 52 2044) : bits64 v < 2^64 := by
  have he := v.2.1.isLt
  have hf := v.2.2.isLt
  unfold bits64
  split_ifs <;> norm_num at * <;> omega

theorem bits64_fraction (v : Encoding 52 2044) : bits64 v % 2^52 = v.2.2.val := by
  have he := v.2.1.isLt
  have hf := v.2.2.isLt
  unfold bits64
  split_ifs <;> norm_num at * <;> omega

theorem bits64_exponent (v : Encoding 52 2044) :
    (bits64 v / 2^52) % 2048 = v.2.1.val := by
  have he := v.2.1.isLt
  have hf := v.2.2.isLt
  unfold bits64
  split_ifs <;> norm_num at * <;> omega

theorem bits64_sign (v : Encoding 52 2044) :
    bits64 v / 2^63 = if v.1 then 1 else 0 := by
  have he := v.2.1.isLt
  have hf := v.2.2.isLt
  unfold bits64
  split_ifs <;> norm_num at * <;> omega

def decode64 (word : Fin (2^64))
    (finite : (word.val / 2^52) % 2048 < 2047) : Encoding 52 2044 :=
  (decide (word.val / 2^63 = 1),
    ⟨(word.val / 2^52) % 2048, finite⟩,
    ⟨word.val % 2^52, Nat.mod_lt _ (by positivity)⟩)

theorem decode64_encode (v : Encoding 52 2044)
    (finite : (bits64 v / 2^52) % 2048 < 2047) :
    decode64 ⟨bits64 v, bits64_bounded v⟩ finite = v := by
  apply Prod.ext
  · simp only [decode64, bits64_sign]
    cases v.1 <;> simp
  · apply Prod.ext <;> apply Fin.ext
    · exact bits64_exponent v
    · exact bits64_fraction v

theorem encode64_decode (word : Fin (2^64))
    (finite : (word.val / 2^52) % 2048 < 2047) :
    bits64 (decode64 word finite) = word.val := by
  have hw := word.isLt
  simp only [bits64, decode64, decide_eq_true_eq]
  split_ifs <;> norm_num at * <;> omega

theorem bits64_significand_parity (v : Encoding 52 2044) :
    bits64 v % 2 = significand v % 2 := by
  unfold bits64 significand
  split_ifs <;> norm_num [Nat.add_mod, Nat.mul_mod]

theorem decode64_bit_value (v : Encoding 52 2044)
    (finite : (bits64 v / 2^52) % 2048 < 2047) :
    value (1/(2 : ℝ)^1074) (decode64 ⟨bits64 v, bits64_bounded v⟩ finite) =
      value (1/(2 : ℝ)^1074) v := by
  rw [decode64_encode]

theorem binary64_nearest_even_bits (x : ℝ)
    (h : ∃ v : Encoding 52 2044,
      IsNearest (1/(2 : ℝ)^1074) x v ∧ bits64 v % 2 = 0) :
    bits64 (nearestEvenEncoding 52 2044 (1/(2 : ℝ)^1074) x) % 2 = 0 := by
  rw [bits64_significand_parity]
  apply nearestEven_tie_policy
  obtain ⟨v, hv, heven⟩ := h
  exact ⟨v, hv, by rwa [← bits64_significand_parity]⟩

#print axioms bits64_bounded
#print axioms bits64_fraction
#print axioms bits64_exponent
#print axioms bits64_sign
#print axioms decode64_encode
#print axioms encode64_decode
#print axioms bits64_significand_parity
#print axioms decode64_bit_value
#print axioms binary64_nearest_even_bits
end
end FindOrbRounding
