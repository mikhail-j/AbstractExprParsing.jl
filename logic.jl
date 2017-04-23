
import Base: hash, ==, show,
            <, <=, >, >=,
            -, +, *, ^, /, \, %,
            ~, &, |, $, >>, <<;

export hash, ==, show,
        <, <=, >, >=,
        -, +, *, ^, /, \, %,
        ~, &, |, $, >>, <<,
        Expression, expr,
        variables, subexpressions;

immutable Expression
	operator::String
	arguments::Tuple
end

Expression(op::String, args::Vararg{Any}) = Expression(op, map(string, args));

function (e::Expression)(args::Vararg{Any})
    if ((length(e.arguments) == 0) && is_logic_symbol(e.operator))
        return Expression(e.operator, map(string, args));
    else
        error("ExpressionError: ", e, " is not a Symbol (Nullary Expression)!");
    end
end

# Hashing Expressions and n-Tuple of Expression(s).

hash(e::Expression, h::UInt) = ((hash(e.operator) $ hash(e.arguments)) $ h);

hash(t_e::Tuple{Vararg{Expression}}, h::UInt) = reduce($, vcat(map(hash, collect(t_e)), h));

<(e1::Expression, e2::Expression) = Expression("<", e1, e2);

<=(e1::Expression, e2::Expression) = Expression("<=", e1, e2);

>(e1::Expression, e2::Expression) = Expression(">", e1, e2);

>=(e1::Expression, e2::Expression) = Expression(">=", e1, e2);

-(e1::Expression) = Expression("-", e1);

+(e1::Expression) = Expression("+", e1);

-(e1::Expression, e2::Expression) = Expression("-", e1, e2);

+(e1::Expression, e2::Expression) = Expression("+", e1, e2);

*(e1::Expression, e2::Expression) = Expression("*", e1, e2);

^(e1::Expression, e2::Expression) = Expression("^", e1, e2);

/(e1::Expression, e2::Expression) = Expression("/", e1, e2);

\(e1::Expression, e2::Expression) = Expression("\\", e1, e2);

%(e1::Expression, e2::Expression) = Expression("<=>", e1, e2);

~(e::Expression) = Expression("~", e);

(&)(e1::Expression, e2::Expression) = Expression("&", e1, e2);

|(e1::Expression, e2::Expression) = Expression("|", e1, e2);

($)(e1::Expression, e2::Expression) = Expression("=/=", e1, e2);

>>(e1::Expression, e2::Expression) = Expression("==>", e1, e2);

<<(e1::Expression, e2::Expression) = Expression("<==", e1, e2);

==(e1::Expression, e2::Expression) = ((e1.operator == e2.operator) && (e1.arguments == e2.arguments));

function show(e::Expression)
    if (length(e.arguments) == 0)
        return e.operator;
    elseif (is_logic_symbol(e.operator))
        return @sprintf("%s(%s)", e.operator, join(map(show, map(Expression, e.arguments)), ", "));
    elseif (length(e.arguments) == 1)
        return @sprintf("%s(%s)", e.operator, show(Expression(e.arguments[1])));
    else
        return @sprintf("(%s)", join(map(show, map(Expression, map(string, e.arguments))), @sprintf(" %s ", e.operator)));
    end
end

function show(io::IO, e::Expression)
    print(io, show(e));
    nothing;
end

function is_logic_symbol(s::String)
    if (length(s) == 0)
        return false;
    else
        return isalpha(s);
    end
end

function is_logic_variable_symbol(s::String)
    return (is_logic_symbol(s) && islower(s[1]));
end

function is_logic_variable(e::Expression)
    return ((length(e.arguments) == 0) && islower(e.operator))
end

"""
    is_logic_proposition_symbol(s)

Return if the given 's' is an initial uppercase String that is not 'TRUE' or 'FALSE'.
"""
function is_logic_proposition_symbol(s::String)
    return (is_logic_symbol(s) && isupper(s[1]) && (s != "TRUE") && (s != "FALSE"));
end

function expr(s::String)
    for (op, new_op) in (("==>", ">>"), ("<==", "<<"), ("<=>", "%"), ("=/=", "\$"))
        s = replace(s, op, new_op);
    end
    return eval(parse(s));
end

function expr(e::Expression)
    return e;
end

function subexpressions(e::Expression)
    local answer::AbstractVector = [e];
    for arg in e.arguments
        answer = vcat(answer, subexpressions(expr(string(arg))));
    end
    return answer;
end

function subexpressions(e::Int)
    local answer::AbstractVector = [Expression(string(e))];
    return answer;
end


function variables(e::Expression)
    return Set(x for x in subexpressions(e) if is_logic_variable(x));
end

type ExpressionNode
    value::Nullable{String}
    parent::Nullable{ExpressionNode}
    children::Array{ExpressionNode, 1}

    function ExpressionNode(;val::Union{Void, String}=nothing, parent::Union{Void, ExpressionNode}=nothing)
        return new(Nullable{String}(val), Nullable{ExpressionNode}(parent), []);
    end
end

function construct_expression_tree(s::String)
    local existing_parenthesis::Int64 = 0;
    local current_string::Array{Char, 1} = Array{Char, 1}([]);
    local current_node::ExpressionNode = ExpressionNode();
    local root_node::ExpressionNode = current_node;
    local isOperator::Bool = false;
    for character in s
        if (character == '(')
            existing_parenthesis = existing_parenthesis + 1;

            println("pre-(: ", String(current_string));

            if (isnull(current_node.value))
                if (!(strip(String(current_string)) == ""))
                    current_node.value = Nullable{String}(String(current_string));
                end
                new_node = ExpressionNode(parent=current_node);
                push!(current_node.children, new_node);
                current_node = new_node;
            else
                new_intermediate_node = ExpressionNode(val=String(current_string), parent=current_node);
                push!(current_node.children, new_intermediate_node)
                current_node = new_intermediate_node;
            end

            if (isOperator)
                isOperator = false;
            end
            current_string = Array{Char, 1}([]);
        elseif (character == ')')
            existing_parenthesis = existing_parenthesis - 1;
            if (isnull(current_node.value) && !isOperator)
                current_node.value = Nullable{String}(String(current_string));
            elseif (length(current_string) != 0)
                push!(current_node.children, ExpressionNode(val=String(current_string), parent=current_node));
            end

            if (isOperator) #operators can't be leaves
                error("ConstructExpressionTreeError: Detected operator at leaf level!");
            end


            print("pre-) value: ", String(current_string),
                " current node value: ", get(current_node.value), " parent node: ");
            if (!isnull(current_node.parent))
                println(get(get(current_node.parent).value));
            else
                println();
            end


            if (!isnull(current_node.parent))   #traverse towards the root
                current_node = get(current_node.parent);
            end
            current_string = Array{Char, 1}([]);
        elseif (character == ',')
            if (strip(String(current_string)) == "")
                error("ConstructExpressionTreeError: Invalid n-Tuple detected!");
            end

            print("current node value: ");
            if (!isnull(current_node.value))
                print(get(current_node.value));
            else
                print("#NULL");
            end
            print(" previous n-ary value: ", String(current_string), " parent node: ");
            if (!isnull(current_node.parent))
                println(get(get(current_node.parent).value));
            else
                println("#NULL");
            end
            print("children: ");
            for c in current_node.children
                print(get(c.value), ",");
            end
            println();

            #push!(current_node.children, ExpressionNode(val=String(current_string), parent=current_node));

            ##check if operator is binary and if we should traverse backward for n-ary operator
            #if (!isnull(current_node.value))
            #    isBinaryOperator::Bool = any((function(c)
            #                                    return c in get(current_node.value);
            #                                end),
            #                                ('+', '-', '*', '/', '\\', '=', '<', '>', '\$', '|', '%', '^', '~', '&'));
            #    if (isBinaryOperator)
            #
            #    end
            #end
            if (isnull(current_node.value))
                current_node.value = Nullable{String}(String(current_string));
            else    #finish any existing binary branch
                push!(current_node.children, ExpressionNode(val=String(current_string), parent=current_node));
            end
            current_node = get(current_node.parent);
            new_nary_node = ExpressionNode(parent=current_node);
            push!(current_node.children, new_nary_node);
            current_node = new_nary_node;

            current_string = Array{Char, 1}([]);
        elseif (character == ' ')   #white space is considered
            push!(current_string, character);
        elseif (character in ('+', '-', '*', '/', '\\', '=', '<', '>', '\$', '|', '%', '^', '~', '&'))
            if (!isOperator)

                print("previous symbol value: ", String(current_string),
                    " current existing node value: ");

                if (!isnull(current_node.value))
                    print(get(current_node.value));
                else
                    print("#NULL");
                end
                print(" parent node: ");
                if (!isnull(current_node.parent))
                    println(get(get(current_node.parent).value));
                else
                    println("#NULL");
                end
                print("children: ");
                for c in current_node.children
                    print(get(c.value), ",");
                end
                println();

                if (isnull(current_node.value))
                    push!(current_node.children, ExpressionNode(val=String(current_string), parent=current_node));
                elseif (!isnull(current_node.parent))
                    new_intermediate_node = ExpressionNode(parent=get(current_node.parent))
                    notFound::Bool = true;
                    for (i, c) in enumerate(get(current_node.parent).children)
                        if (c == current_node)
                            deleteat!(get(current_node.parent).children, i);
                            insert!(get(current_node.parent).children, i, new_intermediate_node);
                            notFound = false;
                            break;
                        end
                    end
                    if (notFound)
                        error("ConstructExpressionTreeError: could not find existing child node!");
                    end
                    current_node.parent = Nullable{ExpressionNode}(new_intermediate_node);
                    push!(new_intermediate_node.children, current_node);
                    current_node = new_intermediate_node;
                else
                    new_root_node = ExpressionNode();
                    push!(new_root_node.children, current_node);
                    current_node.parent = Nullable{ExpressionNode}(new_root_node);
                    current_node = new_root_node;
                    root_node = current_node;
                end
                current_string = Array{Char, 1}([]);
            end
#=
            if (length(current_node.children) > 2)
                error("ConstructBinaryExpressionTreeError: Invalid binary expression tree children count!");
            end
=#
            push!(current_string, character);
            isOperator = true;
        else    #found new symbol  
            if (isOperator) #first character of new token
                if (isnull(current_node.value))
                    current_node.value = Nullable{String}(String(current_string));
                    println("new operator: ", String(current_string));
                else

                    print("previous operator value: ", String(current_string),
                        " current existing node value: ", get(current_node.value), " parent node: ");
                    if (!isnull(current_node.parent) && !isnull(get(current_node.parent).value))
                        println(get(get(current_node.parent).value));
                    else
                        println("#NULL");
                    end

                    new_root_node = ExpressionNode(val=String(current_string));
                    push!(new_root_node.children, current_node);
                    current_node.parent = Nullable{ExpressionNode}(new_root_node);
                    current_node = new_root_node;
                    root_node = current_node;
                end
                current_string = Array{Char, 1}([]);
                isOperator = false;
            end
            push!(current_string, character);
        end


        if (existing_parenthesis < 0)
            error("ConstructExpressionTreeError: Invalid parentheses syntax detected!");
        end
    end
    if (existing_parenthesis != 0)
        error("ConstructExpressionTreeError: Invalid number of parentheses!");
    end
    return root_node;
end

function parse_expression(s::String)
    root_node::ExpressionNode = construct_expression_tree(s);
    return evaluate_expression_tree(root_node);
end

#Some special cases for construct_expression_tree()

#construct_expression_tree("P ==> (Q(1))");

#construct_expression_tree("P ==> (Q(1, 2))");

#construct_expression_tree("Q(P(x) ==> A, S(x)) ==> R(x)");

