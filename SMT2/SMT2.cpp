// SMT1.cpp: определяет точку входа для приложения.
//

using namespace std;

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <vector>
#include <stack>

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

        bool eval(std::vector<bool> values) {
            for (Literal l : literals) {
                if (l.eval(values[l.index])) {
                    return true;
                }
            }
            return false;
        }
    };



public:
    int varsCnt;
    std::vector<Disjunct> clauses;

    Formula(int varsCount, std::vector<std::vector<int>> rawClauses) {
        this->varsCnt = varsCount;
        this->clauses = {};

        for (std::vector<int> literals : rawClauses) {
            Disjunct d(literals);
            this->clauses.push_back(d);
        }
    }


    bool eval(std::vector<bool> values) {
        bool res = false;
        for (Disjunct d : clauses) {
            if (!d.eval(values)) {
                return false;
            }
        }
        return true;
    }


};

class FormulaValue {
public:
    std::vector<bool> values;
    Formula* f;
    bool result;

    FormulaValue(Formula* formula, std::vector<bool> values) {
        f = formula;
        this->values = values;
    }

    FormulaValue(Formula* formula) {
        f = formula;
        this->values = {};
    }


};

std::vector<FormulaValue> solveIterative(Formula formula) {
    std::unique_ptr<std::stack<FormulaValue>> dfsStack = std::make_unique<std::stack<FormulaValue>>();
    std::vector<FormulaValue> results; // = new std::vector<FormulaValue>();
    FormulaValue emptyAssignedFormula(&formula);
    dfsStack->push(emptyAssignedFormula);

    while (!dfsStack->empty())
    {
        FormulaValue currentVariableAssignment = dfsStack->top();
        dfsStack->pop();

        if (currentVariableAssignment.values.size() == formula.varsCnt) {
            // formula is complete and can be evaluated
            currentVariableAssignment.result = currentVariableAssignment.f->eval(currentVariableAssignment.values);
            results.push_back(currentVariableAssignment);
            continue;
        }

        // push left and right "nodes"

        std::vector<bool> valuesWithVarTrue(currentVariableAssignment.values);
        std::vector<bool> valuesWithVarFalse(currentVariableAssignment.values);

        valuesWithVarTrue.push_back(true);
        valuesWithVarFalse.push_back(false);

        FormulaValue formulaWithVarTrue(currentVariableAssignment.f, valuesWithVarTrue);
        FormulaValue formulaWithVarFalse(currentVariableAssignment.f, valuesWithVarFalse);

        dfsStack->push(formulaWithVarTrue);
        dfsStack->push(formulaWithVarFalse);
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


