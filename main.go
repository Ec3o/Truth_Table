package main

import (
	"encoding/json"
	"fmt"
	"github.com/gin-gonic/gin"
	"math"
	"net/http"
	"sort"
	"strings"
	"unicode"
)

type TokenType string

const (
	TokenTypeAnd        TokenType = "&"
	TokenTypeOr         TokenType = "|"
	TokenTypeNot        TokenType = "!"
	TokenTypeImplies    TokenType = "→"
	TokenTypeEquivalent TokenType = "⇔"
	TokenTypeLparen     TokenType = "("
	TokenTypeRparen     TokenType = ")"
	TokenTypeVar        TokenType = "VAR"
)

type Token struct {
	Type  TokenType
	Value string
}

// 解析器函数，用于将表达式解析为抽象AST树
func Lexer(input string) []Token {
	var tokens []Token
	var currentVar string
	//判断字符是否为标准变元
	isVarChar := func(ch rune) bool {
		return (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9')
	}
	//定义匿名函数用于添加变元
	commitVar := func() {
		if currentVar != "" {
			tokens = append(tokens, Token{Type: TokenTypeVar, Value: currentVar})
			currentVar = ""
		}
	}

	for _, ch := range input {
		switch {
		case isVarChar(ch):
			currentVar += string(ch)
		case ch == '&':
			commitVar()
			tokens = append(tokens, Token{Type: TokenTypeAnd})
		case ch == '|':
			commitVar()
			tokens = append(tokens, Token{Type: TokenTypeOr})
		case ch == '!':
			commitVar()
			tokens = append(tokens, Token{Type: TokenTypeNot})
		case ch == '→':
			commitVar()
			tokens = append(tokens, Token{Type: TokenTypeImplies})
		case ch == '⇔':
			commitVar()
			tokens = append(tokens, Token{Type: TokenTypeEquivalent})
		case ch == '(':
			commitVar()
			tokens = append(tokens, Token{Type: TokenTypeLparen})
		case ch == ')':
			commitVar()
			tokens = append(tokens, Token{Type: TokenTypeRparen})
		default:
			// 忽略其他符号
		}
	}

	commitVar() // 提交最后一个变元
	return tokens
}

type Expr interface {
	String() string
	Evaluate(vars map[string]bool) bool
}

func (v Var) String() string { return v.Name }

type Not struct {
	Operand Expr
}
type And struct {
	Left, Right Expr
}
type Or struct {
	Left, Right Expr
}
type Implies struct {
	Left, Right Expr
}
type Equivalent struct {
	Left, Right Expr
}
type Var struct {
	Name string
}

func (n Not) String() string { return "!" + n.Operand.String() }                               //标识符 非 功能实现
func (a And) String() string { return "(" + a.Left.String() + " & " + a.Right.String() + ")" } //标识符 与 功能实现
func (o Or) String() string  { return "(" + o.Left.String() + " | " + o.Right.String() + ")" } //标识符 或 功能实现
func (i Implies) String() string {
	return "(" + i.Left.String() + " → " + i.Right.String() + ")" //标识符 蕴涵 功能实现
}
func (e Equivalent) String() string {
	return "(" + e.Left.String() + " ⇔ " + e.Right.String() + ")" //标识符 等值 功能实现
}

func (v Var) Evaluate(vars map[string]bool) bool { //计算 变量
	value, exists := vars[v.Name]
	if !exists {
		panic(fmt.Sprintf("Variable %s not defined", v.Name))
	}
	return value
}
func (n Not) Evaluate(vars map[string]bool) bool { //计算 非
	return !n.Operand.Evaluate(vars)
}
func (a And) Evaluate(vars map[string]bool) bool { //计算 与
	return a.Left.Evaluate(vars) && a.Right.Evaluate(vars)
}
func (o Or) Evaluate(vars map[string]bool) bool { //计算 或
	return o.Left.Evaluate(vars) || o.Right.Evaluate(vars)
}
func (i Implies) Evaluate(vars map[string]bool) bool { //计算 蕴涵
	// 蕴含 A→B 等价于 ¬A∨B
	return !i.Left.Evaluate(vars) || i.Right.Evaluate(vars)
}
func (e Equivalent) Evaluate(vars map[string]bool) bool { //计算 等值
	// 等值 A⇔B 等价于 (A∧B)∨(¬A∧¬B)
	return (e.Left.Evaluate(vars) && e.Right.Evaluate(vars)) || (!e.Left.Evaluate(vars) && !e.Right.Evaluate(vars))
}

func parsePrimary(tokens []Token, pos *int) (Expr, error) {
	if *pos >= len(tokens) {
		return nil, fmt.Errorf("unexpected end of expression")
	}

	token := tokens[*pos]
	switch token.Type {
	case TokenTypeVar:
		*pos++
		return Var{Name: token.Value}, nil
	case TokenTypeLparen:
		*pos++
		expr, err := parseEquivalent(tokens, pos) // 从最低优先级的操作符‘等值’开始
		if err != nil {
			return nil, err
		}
		if *pos >= len(tokens) || tokens[*pos].Type != TokenTypeRparen {
			return nil, fmt.Errorf("expected ')' at position %d", *pos)
		}
		*pos++
		return expr, nil
	default:
		return nil, fmt.Errorf("unexpected token '%s' at position %d", token.Value, *pos)
	}
}

func parseNot(tokens []Token, pos *int) (Expr, error) {
	if *pos < len(tokens) && tokens[*pos].Type == TokenTypeNot {
		*pos++
		expr, err := parsePrimary(tokens, pos)
		if err != nil {
			return nil, err
		}
		return Not{Operand: expr}, nil
	}
	return parsePrimary(tokens, pos)
}

func parseAnd(tokens []Token, pos *int) (Expr, error) {
	expr, err := parseNot(tokens, pos)
	if err != nil {
		return nil, err
	}

	for *pos < len(tokens) && tokens[*pos].Type == TokenTypeAnd {
		*pos++
		rightExpr, err := parseNot(tokens, pos)
		if err != nil {
			return nil, err
		}
		expr = And{Left: expr, Right: rightExpr}
	}

	return expr, nil
}

func parseOr(tokens []Token, pos *int) (Expr, error) {
	expr, err := parseAnd(tokens, pos)
	if err != nil {
		return nil, err
	}

	for *pos < len(tokens) && tokens[*pos].Type == TokenTypeOr {
		*pos++
		rightExpr, err := parseAnd(tokens, pos)
		if err != nil {
			return nil, err
		}
		expr = Or{Left: expr, Right: rightExpr}
	}

	return expr, nil
}

func parseImplies(tokens []Token, pos *int) (Expr, error) {
	expr, err := parseOr(tokens, pos)
	if err != nil {
		return nil, err
	}

	for *pos < len(tokens) && tokens[*pos].Type == TokenTypeImplies {
		*pos++
		rightExpr, err := parseImplies(tokens, pos) // 递归调用parseImplies来处理蕴涵的右结合性
		if err != nil {
			return nil, err
		}
		expr = Implies{Left: expr, Right: rightExpr}
	}

	return expr, nil
}

// 步骤6:处理等价(⇔)
func parseEquivalent(tokens []Token, pos *int) (Expr, error) {
	expr, err := parseImplies(tokens, pos) //从蕴涵开始解析，因为它具有更高的优先级
	if err != nil {
		return nil, err
	}
	//此循环将处理等价表达式链(例如，a⇔b⇔c)
	for *pos < len(tokens) && tokens[*pos].Type == TokenTypeEquivalent {
		*pos++ //移过'⇔'符号

		//解析等价的右边。注意这一点很重要
		//我们再次调用parseImplies以确保正确的结合性和优先级。
		//这意味着'a⇔b⇔c'被视为'a⇔(b⇔c)'。
		rightExpr, err := parseImplies(tokens, pos)
		if err != nil {
			return nil, err
		}

		//将当前表达式与新的右侧组合成一个新的等效表达式。
		expr = Equivalent{Left: expr, Right: rightExpr}
	}

	return expr, nil
}

func CORSMiddleware() gin.HandlerFunc {
	return func(c *gin.Context) {
		c.Writer.Header().Set("Access-Control-Allow-Origin", "*")
		c.Writer.Header().Set("Access-Control-Allow-Credentials", "true")
		c.Writer.Header().Set("Access-Control-Allow-Headers", "Content-Type, Content-Length, Accept-Encoding, X-CSRF-Token, Authorization, accept, origin, Cache-Control, X-Requested-With")
		c.Writer.Header().Set("Access-Control-Allow-Methods", "POST, OPTIONS, GET, PUT, DELETE")

		if c.Request.Method == "OPTIONS" {
			c.AbortWithStatus(http.StatusNoContent)
			return
		}

		c.Next()
	}
}

func main() {
	input := "p|q&r" // 示例输入
	tokens := Lexer(input)
	fmt.Println("Tokens:", tokens)

	var pos int
	ast, err := parseOr(tokens, &pos) // 从最低优先级的逻辑“或”开始解析
	if err != nil {
		fmt.Println("Error parsing expression:", err)
		return
	}
	variables := ExtractVariables(input)
	printTruthTableForSubexpressions(ast, variables)
	printAST(ast, 0)
	fmt.Println("AST:", ast.String())
	println(truthTableToJson(ast, variables))
	r := gin.Default()
	r.Use(CORSMiddleware())
	r.GET("/api/data", ExpressHandler)
	r.LoadHTMLFiles("index.html")
	r.GET("/", func(c *gin.Context) {
		c.HTML(200, "index.html", 0)
	})
	r.Run(":8000")
}

// 函数功能：递归呈现抽象AST树结构
func printAST(node Expr, level int) {
	indent := ""
	for i := 0; i < level; i++ {
		indent += "  "
	}

	switch n := node.(type) {
	case Var:
		fmt.Printf("%sVar: %s\n", indent, n.Name)
	case Not:
		fmt.Printf("%sNot\n", indent)
		printAST(n.Operand, level+1)
	case And:
		fmt.Printf("%sAnd\n", indent)
		printAST(n.Left, level+1)
		printAST(n.Right, level+1)
	case Or:
		fmt.Printf("%sOr\n", indent)
		printAST(n.Left, level+1)
		printAST(n.Right, level+1)
	default:
		fmt.Printf("%sUnknown node type\n", indent)
	}
}

func ExtractVariables(expression string) []string {
	varSet := make(map[string]struct{}) // 使用map来存储唯一变元
	var currentVar strings.Builder

	for _, char := range expression {
		if unicode.IsLetter(char) {
			// 如果字符是字母，追加到当前变元
			currentVar.WriteRune(char)
		} else if currentVar.Len() > 0 {
			// 遇到非字母字符且currentVar不为空时，表示一个变元结束
			varSet[currentVar.String()] = struct{}{}
			currentVar.Reset()
		}
	}

	// 检查表达式末尾是否有未处理的变元
	if currentVar.Len() > 0 {
		varSet[currentVar.String()] = struct{}{}
	}

	// 将变元从map转移到slice中，并排序
	var variables []string
	for varName := range varSet {
		variables = append(variables, varName)
	}
	sort.Strings(variables)

	return variables
}

func truthTable(ast Expr, variables []string) {
	var totalCombinations int = int(math.Pow(2, float64(len(variables))))
	fmt.Println("Variables:", variables)
	for i := 0; i < totalCombinations; i++ {
		var combination = make(map[string]bool)
		for j, variable := range variables {
			// 根据位的值将true和false改为1和0
			combination[variable] = ((i >> j) & 1) == 1
		}
		result := ast.Evaluate(combination)
		printCombination(combination, result, variables)
	}
}

func printCombination(combination map[string]bool, result bool, variables []string) {
	// 按照变量列表的顺序打印，确保输出的顺序一致
	for _, varName := range variables {
		// 将bool值转换为0和1进行打印
		varValue := 0
		if combination[varName] {
			varValue = 1
		}
		fmt.Printf("%s: %d, ", varName, varValue)
	}
	// 将结果的bool值也转换为0和1
	resultValue := 0
	if result {
		resultValue = 1
	}
	fmt.Printf("Result: %d\n", resultValue)
}

func printTruthTableForSubexpressions(expr Expr, parentVars []string) {
	// 首先，提取当前表达式所涉及的所有唯一变量
	variables := extractVariablesFromExpr(expr, parentVars)

	// 打印当前表达式的真值表
	fmt.Println("Truth table for expression:", expr.String())
	truthTable(expr, variables)

	// 如果当前表达式是复合表达式，则递归地为其子表达式打印真值表
	switch e := expr.(type) {
	case And:
		printTruthTableForSubexpressions(e.Left, variables)
		printTruthTableForSubexpressions(e.Right, variables)
	case Or:
		printTruthTableForSubexpressions(e.Left, variables)
		printTruthTableForSubexpressions(e.Right, variables)
	case Not:
		printTruthTableForSubexpressions(e.Operand, variables)
		// Var类型的表达式没有子表达式，所以不需要进一步递归
	}
}

// 提取表达式中的变量（递归地处理复合表达式）
func extractVariablesFromExpr(expr Expr, parentVars []string) []string {
	var variables []string
	// 根据表达式类型递归提取变量
	switch e := expr.(type) {
	case And:
		variables = append(variables, extractVariablesFromExpr(e.Left, parentVars)...)
		variables = append(variables, extractVariablesFromExpr(e.Right, parentVars)...)
	case Or:
		variables = append(variables, extractVariablesFromExpr(e.Left, parentVars)...)
		variables = append(variables, extractVariablesFromExpr(e.Right, parentVars)...)
	case Not:
		variables = append(variables, extractVariablesFromExpr(e.Operand, parentVars)...)
	case Var:
		variables = append(variables, e.Name)
	}
	// 确保变量列表中的变量是唯一的
	variables = append(variables, parentVars...)
	sort.Strings(variables)
	return removeDuplicates(variables)
}

// 去除字符串切片中的重复项
func removeDuplicates(elements []string) []string {
	encountered := map[string]bool{}
	result := []string{}

	for v := range elements {
		if encountered[elements[v]] == true {
			// Do not add duplicate.
		} else {
			encountered[elements[v]] = true
			result = append(result, elements[v])
		}
	}
	return result
}

func evaluateExpressionAndSubexpressions(expr Expr, combination map[string]bool) map[string]int {
	result := make(map[string]int)

	// 计算当前表达式的值
	if expr.Evaluate(combination) {
		result[expr.String()] = 1
	} else {
		result[expr.String()] = 0
	}

	// 根据表达式类型，递归处理子表达式
	switch e := expr.(type) {
	case And:
		mergeResults(result, evaluateExpressionAndSubexpressions(e.Left, combination))
		mergeResults(result, evaluateExpressionAndSubexpressions(e.Right, combination))
	case Or:
		mergeResults(result, evaluateExpressionAndSubexpressions(e.Left, combination))
		mergeResults(result, evaluateExpressionAndSubexpressions(e.Right, combination))
	case Not:
		mergeResults(result, evaluateExpressionAndSubexpressions(e.Operand, combination))
	case Implies:
		mergeResults(result, evaluateExpressionAndSubexpressions(e.Left, combination))
		mergeResults(result, evaluateExpressionAndSubexpressions(e.Right, combination))
	case Equivalent:
		mergeResults(result, evaluateExpressionAndSubexpressions(e.Left, combination))
		mergeResults(result, evaluateExpressionAndSubexpressions(e.Right, combination))
	}

	return result
}

// 辅助函数：将子表达式的结果合并到主结果集中
func mergeResults(mainResult, subResult map[string]int) {
	for k, v := range subResult {
		mainResult[k] = v
	}
}

func truthTableToJson(expr Expr, variables []string) (string, error) {
	var totalCombinations int = int(math.Pow(2, float64(len(variables))))
	results := make([]map[string]int, 0)

	for i := 0; i < totalCombinations; i++ {
		var combination = make(map[string]bool)
		for j, variable := range variables {
			// 根据当前索引i和变量的位置j计算每个变量的布尔值
			combination[variable] = (i>>j)&1 == 1
		}
		// 对当前的变量组合求值，并获取表达式及其子表达式的结果
		result := evaluateExpressionAndSubexpressions(expr, combination)
		results = append(results, result)
	}

	// 将结果序列化为JSON字符串
	jsonResults, err := json.Marshal(results)
	if err != nil {
		return "", fmt.Errorf("error marshalling results to JSON: %v", err)
	}
	return string(jsonResults), nil
}

func ExpressHandler(c *gin.Context) {
	expression := c.Query("exp") //获取表达式参数
	tokens := Lexer(expression)  //解析表达式为Token块
	var pos int
	ast, err := parseEquivalent(tokens, &pos)
	printAST(ast, 0)
	if err != nil {
		fmt.Println("Error parsing expression:", err)
		c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
		return
	}
	variables := ExtractVariables(expression)           //提取所有的变量
	truthTable, err := truthTableToJson(ast, variables) // 修改了函数名
	if err != nil {
		fmt.Println("Error generating truth table:", err)
		c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()}) // 修改了错误消息
		return
	}
	c.Header("Content-Type", "application/json")
	c.JSON(http.StatusOK, truthTable)
}
