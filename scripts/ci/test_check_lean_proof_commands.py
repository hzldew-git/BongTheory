"""Regression checks for the supplemental source gate; no files are created."""

import unittest

from check_lean_proof_commands import findings, mask_comments


class ProofCommandScanTests(unittest.TestCase):
    def test_published_ci_false_positive(self):
        self.assertEqual(findings("/-!\nwithout an axiom, `sorry`, or hidden identification\n-/"), [])

    def test_nested_comments_and_line_comments(self):
        self.assertEqual(findings("/- sorry /- axiom -/ admit -/\n-- sorryAx\nexample : True := by trivial"), [])

    def test_each_actual_forbidden_token(self):
        for token in ("sorry", "admit", "sorryAx", "axiom"):
            with self.subTest(token=token):
                self.assertEqual(findings(f"\n  {token} x"), [(2, token)])

    def test_code_after_nested_comment_is_checked(self):
        self.assertEqual(findings("/- outer /- inner -/ -/ sorry"), [(1, "sorry")])

    def test_same_line_comment_does_not_hide_earlier_code(self):
        self.assertEqual(findings("example : True := by sorry -- commentary"), [(1, "sorry")])

    def test_block_comment_preserves_line_numbers(self):
        source = "/- first\n/- nested -/\nlast -/\nexample : True := by sorry"
        self.assertEqual(findings(source), [(4, "sorry")])
        self.assertEqual(len(mask_comments(source)), len(source))

    def test_crlf_preserved(self):
        self.assertEqual(findings("/- sorry\r\n-/\r\naxiom x : True"), [(3, "axiom")])

    def test_comment_delimiters_in_strings(self):
        self.assertEqual(findings('def s := "/- --"\nexample : True := by sorry'), [(2, "sorry")])

    def test_escaped_quote(self):
        self.assertEqual(findings('def s := "\\\"/-"\naxiom x : True'), [(2, "axiom")])

    def test_raw_quoted_comment_markers(self):
        self.assertEqual(findings('def s := r##"/- \\" --"##\nadmit'), [(2, "admit")])

    def test_character_quote_and_primed_identifier(self):
        self.assertEqual(findings("def s' := '\"'\nexample : True := by sorry"), [(2, "sorry")])

    def test_identifier_boundaries(self):
        self.assertEqual(findings("sorryName axiomFree sorry_lemma x.sorryAx' αsorry sorryβ"), [])
        self.assertEqual(findings("_root_.sorryAx"), [(1, "sorryAx")])

    def test_quoted_forbidden_words_are_conservatively_reported(self):
        self.assertEqual(findings('def s := "sorry"'), [(1, "sorry")])

    def test_interpolated_terms_fail_closed(self):
        for source in ('def s := s!"{sorry}"', 'def s := "{nested}"'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                findings(source)

    def test_escaped_identifier_comment_markers_do_not_hide_code(self):
        for token in ("sorry", "axiom", "admit", "sorryAx"):
            source = f"def «/-» : Nat := 0\n{token} x\n-- -/"
            with self.subTest(token=token):
                self.assertEqual(findings(source), [(2, token)])

    def test_nested_interpolated_quote_attack_fails_closed(self):
        for token in ("sorry", "axiom", "admit", "sorryAx"):
            source = 'def scannerProbe : String := s!"{"/-"}"\n' + token + ' x\n-- -/'
            with self.subTest(token=token), self.assertRaises(ValueError):
                findings(source)

    def test_escaped_identifier_line_marker(self):
        self.assertEqual(findings("def «--» : Nat := 0\nsorry"), [(2, "sorry")])

    def test_unterminated_input_fails_closed(self):
        for source in ("/- open", '"open', 'r#"open', "«open"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                findings(source)


if __name__ == "__main__":
    unittest.main()
