# pypl
Generating latex table for PL

## To get started
```
$ virtialenv pypl
$ source pyply/bin/activate
$ pip install -r requirements.txt
```

## To run
```
$ python pypl.py
PL> table (P & Q) | !G
\begin{tabular}{|c|c|c|c|c|c|}
	\hline
	$P$ & $Q$ & $(P \wedge Q)$ & $G$ & $\neg G$ & $((P \wedge Q) \vee \neg G)$ \\
	\hline
	T & T & T & T & F & T \\
	T & T & T & F & T & T \\
	T & F & F & T & F & F \\
	T & F & F & F & T & T \\
	F & T & F & T & F & F \\
	F & T & F & F & T & T \\
	F & F & F & T & F & F \\
	F & F & F & F & T & T \\
	\hline
\end{tabular}
PL> derive (A -> B) and (D -> (C and A))
$V_I(((A \supset B) \wedge (D \supset (C \wedge A))))$ = 1\\
	\indent iff \quad $V_I((A \supset B))$ = 1 and $V_I((D \supset (C \wedge A)))$ = 1 \\
	\indent iff \quad [$V_I(A)$ = 0 or $V_I(B)$ = 1] and $V_I((D \supset (C \wedge A)))$ = 1 \\
	\indent iff \quad [$I(A)$ = 0 or $I(B)$ = 1] and $V_I((D \supset (C \wedge A)))$ = 1 \\
	\indent iff \quad [$I(A)$ = 0 or $I(B)$ = 1] and [$V_I(D)$ = 0 or $V_I((C \wedge A))$ = 1] \\
	\indent iff \quad [$I(A)$ = 0 or $I(B)$ = 1] and [$I(D)$ = 0 or $V_I((C \wedge A))$ = 1] \\
	\indent iff \quad [$I(A)$ = 0 or $I(B)$ = 1] and [$I(D)$ = 0 or [$V_I(C)$ = 1 and $V_I(A)$ = 1]] \\
	\indent iff \quad [$I(A)$ = 0 or $I(B)$ = 1] and [$I(D)$ = 0 or [$I(C)$ = 1 and $I(A)$ = 1]] \\
PL> ^D
$ 
```
