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
PL> (P & Q) | !G
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
PL> ^D
$ 
```
