# Mini-Prolog-Interpreter
[Prolog](https://en.wikipedia.org/wiki/Prolog) is a logic programming language written using clauses and goals. Clauses can be either facts or rules. Facts are the most basic clause; it is a function that declares a specific relationship between two entities. For example, we can say:
```
neighbors(spongebob, patrick)
```
and then use these simple facts to develop rules. For example:
```
friends(X, Y) :- neighbors(X, Y)
```
thus extending the relationships between individuals. Note that variables are written using capital letters while constants are lower case. 

This project is an mini interpreter for Prolog built using Python3. The intepreter uses an abstract syntax tree to process the rules and syntax of Prolog. There are also functions to handle the basic logic of Prolog such as substitution and unifying
