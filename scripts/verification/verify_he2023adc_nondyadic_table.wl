(* Independent symbolic check of He (2025), Lemma 4.7(i), pp. 993--994.
   Version-of-record SHA-256:
   E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6 *)

columns = {1, 2};
classes = {"1", "Delta", "pi", "DeltaPi"};
unitClasses = {"1", "Delta"};
uniformizerClasses = {"pi", "DeltaPi"};

deltaTwist["1"] = "Delta";
deltaTwist["Delta"] = "1";
deltaTwist["pi"] = "DeltaPi";
deltaTwist["DeltaPi"] = "pi";

atomRank["H"] = 2;
atomRank[_List] = 1;
atomJ0Rank["H"] = 2;
atomJ0Rank[{c_}] := If[MemberQ[unitClasses, c], 1, 0];
atomJ1Rank["H"] = 0;
atomJ1Rank[{c_}] := If[MemberQ[uniformizerClasses, c], 1, 0];

evenTail[1, "1"] = {};
evenTail[2, "1"] = {{"1"}, {"Delta"}, {"pi"}, {"DeltaPi"}};
evenTail[1, "Delta"] = {{"1"}, {"Delta"}};
evenTail[2, "Delta"] = {{"pi"}, {"DeltaPi"}};
evenTail[1, "pi"] = {{"1"}, {"pi"}};
evenTail[2, "pi"] = {{"Delta"}, {"DeltaPi"}};
evenTail[1, "DeltaPi"] = {{"1"}, {"DeltaPi"}};
evenTail[2, "DeltaPi"] = {{"Delta"}, {"pi"}};

evenHyperbolicCount[k_, 1, "1"] = k;
evenHyperbolicCount[k_, 2, "1"] = k - 2;
evenHyperbolicCount[k_, _, _] = k - 1;

oddTail[1, c_] := {{c}};
oddTail[2, "1"] = {{"pi"}, {"DeltaPi"}, {"Delta"}};
oddTail[2, "Delta"] = {{"pi"}, {"DeltaPi"}, {"1"}};
oddTail[2, "pi"] = {{"1"}, {"Delta"}, {"DeltaPi"}};
oddTail[2, "DeltaPi"] = {{"1"}, {"Delta"}, {"pi"}};

oddHyperbolicCount[k_, 1] = k;
oddHyperbolicCount[k_, 2] = k - 1;

tailRank[tail_] := Total[atomRank /@ tail];
tailJ0Rank[tail_] := Total[atomJ0Rank /@ tail];
tailJ1Rank[tail_] := Total[atomJ1Rank /@ tail];

evenRank[k_, nu_, c_] :=
  2 evenHyperbolicCount[k, nu, c] + tailRank[evenTail[nu, c]];
evenJ0Rank[k_, nu_, c_] :=
  2 evenHyperbolicCount[k, nu, c] + tailJ0Rank[evenTail[nu, c]];
evenJ1Rank[k_, nu_, c_] := tailJ1Rank[evenTail[nu, c]];

oddRank[k_, nu_, c_] :=
  2 oddHyperbolicCount[k, nu] + tailRank[oddTail[nu, c]];
oddJ0Rank[k_, nu_, c_] :=
  2 oddHyperbolicCount[k, nu] + tailJ0Rank[oddTail[nu, c]];
oddJ1Rank[k_, nu_, c_] := tailJ1Rank[oddTail[nu, c]];

evenDefinedAssumption[k_, 2, "1"] := k >= 2;
evenDefinedAssumption[k_, _, _] := k >= 1;
oddDefinedAssumption[k_, 1, _] := k >= 0;
oddDefinedAssumption[k_, 2, _] := k >= 1;

evenRankChecks = Flatten@Table[
  FullSimplify[evenRank[k, nu, c] == 2 k,
    Assumptions -> Element[k, Integers] && evenDefinedAssumption[k, nu, c]],
  {nu, columns}, {c, classes}];

oddRankChecks = Flatten@Table[
  FullSimplify[oddRank[k, nu, c] == 2 k + 1,
    Assumptions -> Element[k, Integers] && oddDefinedAssumption[k, nu, c]],
  {nu, columns}, {c, classes}];

zeroOneChecks = Join[
  Flatten@Table[
    FullSimplify[evenJ0Rank[k, nu, c] + evenJ1Rank[k, nu, c] ==
      evenRank[k, nu, c],
      Assumptions -> Element[k, Integers] &&
        evenDefinedAssumption[k, nu, c]],
    {nu, columns}, {c, classes}],
  Flatten@Table[
    FullSimplify[oddJ0Rank[k, nu, c] + oddJ1Rank[k, nu, c] ==
      oddRank[k, nu, c],
      Assumptions -> Element[k, Integers] && oddDefinedAssumption[k, nu, c]],
    {nu, columns}, {c, classes}]
  ];

uniformizerJ0Checks = Join[
  Flatten@Table[
    FullSimplify[evenJ0Rank[k, nu, c] == 2 k - 1,
      Assumptions -> Element[k, Integers] && k >= 1],
    {nu, columns}, {c, uniformizerClasses}],
  Flatten@Table[
    FullSimplify[oddJ0Rank[k, nu, c] == 2 k,
      Assumptions -> Element[k, Integers] && k >= 1],
    {nu, columns}, {c, uniformizerClasses}]
  ];

firstUnitJ0Checks = Join[
  Flatten@Table[
    FullSimplify[evenJ0Rank[k, 1, c] == 2 k,
      Assumptions -> Element[k, Integers] && k >= 1],
    {c, unitClasses}],
  Flatten@Table[
    FullSimplify[oddJ0Rank[k, 1, c] == 2 k + 1,
      Assumptions -> Element[k, Integers] && k >= 0],
    {c, unitClasses}]
  ];

binaryRows = Tuples[{columns, classes}];
binaryDefinedRows = DeleteCases[binaryRows, {2, "1"}];
unaryRows = Tuples[{columns, classes}];
unaryDefinedRows = Select[unaryRows, First[#] == 1 &];
quaternaryRows = Table[{{nu, c},
    Join[Table["H", {evenHyperbolicCount[2, nu, c]}], evenTail[nu, c]]},
  {nu, columns}, {c, classes}];
quaternaryRows = Flatten[quaternaryRows, 1];
exceptionalQuaternaryTail =
  {{"1"}, {"Delta"}, {"pi"}, {"DeltaPi"}};
nonexceptionalQuaternaryRows =
  Select[quaternaryRows, First[#] != {2, "1"} &];

result = <|
  "evenRows" -> And @@ evenRankChecks,
  "oddRows" -> And @@ oddRankChecks,
  "jordanZeroOne" -> And @@ zeroOneChecks,
  "uniformizerJ0Ranks" -> And @@ uniformizerJ0Checks,
  "firstUnitJ0Ranks" -> And @@ firstUnitJ0Checks,
  "deltaTwistInvolution" -> And @@ (deltaTwist[deltaTwist[#]] == # & /@ classes),
  "unarySecondColumnOmitted" ->
    Sort[Complement[unaryRows, unaryDefinedRows]] ==
      Sort[({2, #} & /@ classes)],
  "unaryDefinedCount" -> Length[unaryDefinedRows] == 4,
  "binaryUndefinedRow" -> Complement[binaryRows, binaryDefinedRows] == {{2, "1"}},
  "binaryDefinedCount" -> Length[binaryDefinedRows] == 7,
  "exceptionalQuaternaryRow" ->
    Cases[quaternaryRows, {{2, "1"}, row_} :> row] ==
      {exceptionalQuaternaryTail},
  "otherQuaternaryRowsContainH" ->
    And @@ (MemberQ[Last[#], "H"] & /@ nonexceptionalQuaternaryRows)
  |>;

Print[result];
If[And @@ Values[result], Exit[0], Exit[1]];
