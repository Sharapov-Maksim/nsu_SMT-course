using namespace std;

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <algorithm>
#include <vector>
#include <map>
#include <stack>
#include <set>
#include <cassert>


class CnfParser {
public:
    CnfParser(const std::string& filename) : filename_(filename) {}

    bool parse() {
        std::ifstream file(filename_);
        if (!file) {
            std::cerr << "Error: unable to open file " << filename_ << std::endl;
            return false;
        }

        std::string line;
        while (std::getline(file, line)) {
            if (line.empty() || line[0] == 'c') {
                // skip empty lines and comments
                continue;
            }

            if (line[0] == 'p') {
                // parse problem line (e.g., "p cnf 3 4")
                parseProblemLine(line);
            }
            else {
                // parse clause line (e.g., "1 2 3 0")
                parseClauseLine(line);
            }
        }

        file.close();
        return true;
    }

    // getters for parsed data
    int getNumVariables() { return num_variables_; }
    int getNumClauses() { return num_clauses_; }
    const std::vector<std::vector<int>>& getClauses() { return clauses_; }

private:
    void parseProblemLine(const std::string& line) {
        std::istringstream iss(line);
        std::string token;
        iss >> token; // "p"
        iss >> token; // "cnf"
        iss >> num_variables_;
        iss >> num_clauses_;
    }

    void parseClauseLine(const std::string& line) {
        std::istringstream iss(line);
        std::vector<int> clause;
        int literal;
        while (iss >> literal) {
            if (literal == 0) {
                // end of clause marker
                break;
            }
            clause.push_back(literal);
        }
        clauses_.push_back(clause);
    }

    std::string filename_;
    int num_variables_;
    int num_clauses_;
    std::vector<std::vector<int>> clauses_;
};

class Formula {
    class Literal {
    public:
        bool isVariable; // fasle for constant
        bool isPositive;
        int index;

        bool value; // value of cosntant

        Literal(int index, bool isPositive) {
            this->index = index;
            this->isPositive = isPositive;
            this->isVariable = true;
        }

        Literal(bool value) {
            this->value = value;
            this->isVariable = false;
        }

        Literal(const Literal& other) : isVariable(other.isVariable), isPositive(other.isPositive), index(other.index), value(other.value) {}

        bool eval(bool value) {
            return (this->isPositive && value == true) || (!this->isPositive && value == false);
        }
    };

    class Disjunct {
    public:
        std::vector<Literal> literals;

        Disjunct(std::vector<int> literals) {
            this->literals = {};
            for (int l : literals) {
                bool isPositive = l >= 0;
                int index = abs(l) - 1;
                Literal liter(index, isPositive);
                this->literals.push_back(liter);
            }
        }

        Disjunct(const Disjunct& other) : literals(other.literals) {}


        bool eval(std::map<int, bool> values) {
            for (Literal l : literals) {
                auto idxValPair = values.find(l.index);
                assert(idxValPair != values.end());
                if (l.eval(idxValPair->second)) {
                    return true;
                }
            }
            return false;
        }

        bool containsVar(int index, bool positive) {
            for (Literal l : literals) {
                if (l.index == index && l.isPositive == positive) {
                    return true;
                }
            }
            return false;
        }


        /* Returns false if disjunct can be evaluated to false. 
        Returns true - otherwise, when it is not enough values to evaluate to false, or evaluates to true. */
        bool partiallyEvaluate(std::map<int, bool> values) {
            assert(literals.size() > 0);
            for (Literal l : literals) {
                auto idxValPair = values.find(l.index);
                if (idxValPair == values.end()) {
                    // we cant say if disjunct is false, no value for literal
                    return true;
                }
                if (l.eval(idxValPair->second)) {
                    // disjunct is true
                    return true;
                }
            }
            // discjunct contains no undefined and no true-evaluated variables, then disjunct is false.
            return false;
        }

        /*
        0 - not atomic
        +<varIdx> - atomic positive variable
        -<varIdx> - atomic negative variable
        */
        int atomicDisjunct() {
            assert(literals.size() > 0);
            if (literals.size() != 1) {
                return 0;
            }
            Literal lit = literals[0];
            if (lit.isPositive) {
                return lit.index;
            }
            else {
                return -1 * lit.index;
            }
        }
    };



public:
    std::set<int> variablesNotAssigned;
    std::vector<Disjunct> clauses;

    Formula() : variablesNotAssigned({}), clauses({}) {}

    Formula(int varsCount, std::vector<std::vector<int>> rawClauses) {
        this->variablesNotAssigned = {};
        this->clauses = {};

        for (int i = 0; i < varsCount; i++) {
            this->variablesNotAssigned.insert(i);
        }

        for (std::vector<int> literals : rawClauses) {
            Disjunct d(literals);
            this->clauses.push_back(d);
        }
    }

    void simplify(std::map<int, bool> values) {
        for (const int& varIdx : variablesNotAssigned) {
            auto idxValPair = values.find(varIdx);
            if (idxValPair != values.end()) {
                bool varVal = idxValPair->second;
                // heuristic 2: remove disjuncts already true
                clauses.erase(std::remove_if(clauses.begin(), clauses.end(), [varIdx, varVal](Disjunct clause) {
                    // if disjunct contains variable with corresponding positiveness
                    return clause.containsVar(varIdx, varVal);
                    }), clauses.end());
            }
        }

        // cleanup the variablesNotAssigned set
        for (const auto& idxValPair : values) {
            int idx = idxValPair.first;
            auto it = variablesNotAssigned.find(idx);
            if (it != variablesNotAssigned.end()) {
                variablesNotAssigned.erase(it);
            }
        }
    }

    bool isEvaluateble(std::map<int, bool> values) {
        for (const int& varIdx : variablesNotAssigned) {
            auto value = values.find(varIdx);
            if (value == values.end()) {
                return false;
            }
        }
        return true;
    }

    bool eval(std::map<int, bool> values) {
        bool res = false;
        for (Disjunct d : clauses) {
            if (!d.eval(values)) {
                return false;
            }
        }
        return true;
    }

    /* Returns false if formula can be evaluated to false.
       Returns true - otherwise, when it is not enough values to evaluate to false, or evaluates to true. */
    bool partiallyEvaluate(std::map<int, bool> values) {
        assert(clauses.size() > 0);
        bool res = false;
        for (Disjunct d : clauses) {
            if (d.partiallyEvaluate(values) == false) {
                // one of disjuncts evaluates to false, so whole formula evaluates to false
                return false;
            }
        }
        return true;
    }

    std::set<int> atomicNotAssignedDisjuncts() {
        assert(clauses.size() > 0);
        std::set<int> result = {};
        for (Disjunct d : clauses) {
            int atomic = d.atomicDisjunct();
            if (atomic != 0) {
                auto it = variablesNotAssigned.find(abs(atomic));
                if (it != variablesNotAssigned.end()) {
                    result.insert(atomic);
                }
            }
        }
        return result;
    }

    // Copy Constructor
    Formula(const Formula& other) : variablesNotAssigned(other.variablesNotAssigned), clauses(other.clauses) {}
};

class FormulaValue {
public:
    std::map<int, bool> values;
    Formula f;
    bool result;

    FormulaValue(const Formula& formula) {
        f = formula;
        this->values = {};
        result = false;
    }

    // Copy Constructor
    FormulaValue(const FormulaValue& other) : values(other.values), f(other.f), result(other.result) {}
};

class VariableValue { // TODO use just bool?
public:
    int varIndex;
    bool value;
};

std::vector<FormulaValue> solveIterative(Formula formula) {
    std::unique_ptr<std::stack<FormulaValue>> dfsStack = std::make_unique<std::stack<FormulaValue>>();
    std::vector<FormulaValue> results; // = new std::vector<FormulaValue>();
    FormulaValue emptyAssignedFormula(formula);
    dfsStack->push(emptyAssignedFormula);

    while (!dfsStack->empty())
    {
        FormulaValue currentVariableAssignment = dfsStack->top();
        dfsStack->pop();
        currentVariableAssignment.f.simplify(currentVariableAssignment.values);
        if (currentVariableAssignment.f.isEvaluateble(currentVariableAssignment.values)) {
            // formula is complete and can be evaluated
            currentVariableAssignment.result = currentVariableAssignment.f.eval(currentVariableAssignment.values);

            results.push_back(currentVariableAssignment);
            if (currentVariableAssignment.result) {
                // heuristic 1 (lab 3): finish search on first positive result
                return results;
            }
        }

        if (currentVariableAssignment.f.partiallyEvaluate(currentVariableAssignment.values) == false) {
            // heurisitc 3 (lab 4): formula evaluates to false, skip this decision tree branch
            continue;
        }

        // if formula contains more variables 
        if (!currentVariableAssignment.f.variablesNotAssigned.empty()) {
            // find next variable to assign value
            int index;
            std::set<int> atomicDisjuncts = currentVariableAssignment.f.atomicNotAssignedDisjuncts();
            if (atomicDisjuncts.size() > 0) {
                // heuristic 4 (lab 5): select some atomic disjunct, continue search for branch when it is true
                int variableWithPositiveness = *atomicDisjuncts.begin();
                index = abs(variableWithPositiveness);
                bool positiveness = variableWithPositiveness > 0;

                FormulaValue newFormula(currentVariableAssignment);
                // Insert element into the map
                auto insertionResult0 = newFormula.values.insert({ index, positiveness });
                assert(insertionResult0.second); // check that inserted key did not exist before

                // push only one node
                dfsStack->push(newFormula);
            }
            else {
                index = *(currentVariableAssignment.f.variablesNotAssigned).begin();
                FormulaValue formulaWithVarTrue(currentVariableAssignment);
                FormulaValue formulaWithVarFalse(currentVariableAssignment);

                // Insert element into the map
                auto insertionResult0 = formulaWithVarTrue.values.insert({ index, true });
                assert(insertionResult0.second); // check that inserted key did not exist before
                auto insertionResult1 = formulaWithVarFalse.values.insert({ index, false });
                assert(insertionResult1.second);

                // push left and right "nodes"
                dfsStack->push(formulaWithVarTrue);
                dfsStack->push(formulaWithVarFalse);
            }

            
            
        }
    }

    return results;
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cerr << "Error: no filename provided" << std::endl;
        return 1;
    }

    std::string filename = argv[1];
    CnfParser parser(filename);
    if (!parser.parse()) {
        return 1;
    }
    int varsCnt = parser.getNumVariables();
    Formula baseFormula(varsCnt, parser.getClauses());

    std::vector<FormulaValue> allAssignments = solveIterative(baseFormula);

    for (FormulaValue formVal : allAssignments) {
        if (formVal.values.size() != varsCnt) {
            std::cerr << "Error: size differ " << formVal.values.size() << "!=" << varsCnt;
            return 1;
        }

        if (formVal.result == true) {
            std::cout << "s SATISFIABLE" << std::endl;
            std::cout << "v ";
            for (int i = 0; i < formVal.values.size(); i++) {
                bool v = formVal.values[i];
                if (!v) {
                    std::cout << "-";
                }
                std::cout << (i + 1) << " ";
            }
            std::cout << "0" << std::endl;
            return 0;
        }
    }

    std::cout << "s UNSATISFIABLE" << std::endl;

    return 0;
}

