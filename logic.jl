
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

Expression(op::String, args::Vararg{Any}) = Expression(op, map(Expression, args));

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
        #answer = vcat(answer, subexpressions(expr(string(arg))));
        answer = vcat(answer, subexpressions(arg));
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

function identify_tokens(s::String)
    local existing_parenthesis::Int64 = 0;
    local queue::Array{String, 1} = Array{String, 1}([]);
    local current_string::Array{Char, 1} = Array{Char, 1}([]);
    local isOperator::Bool = false;
    for character in s
        if (character == '(')
            existing_parenthesis = existing_parenthesis + 1;

            if (strip(String(current_string)) != "")
                push!(queue, strip(String(current_string)));
            end
            push!(queue, "(");

            if (isOperator)
                isOperator = false;
            end
            current_string = Array{Char, 1}([]);
        elseif (character == ')')
            existing_parenthesis = existing_parenthesis - 1;

            if (strip(String(current_string)) != "")
                push!(queue, strip(String(current_string)));
            end
            push!(queue, ")");

            if (isOperator) #operators can't be leaves
                error("ConstructExpressionTreeError: Detected operator at leaf level!");
            end

            current_string = Array{Char, 1}([]);
        elseif (character == ',')
            if (strip(String(current_string)) == "")
                if (queue[length(queue)] == ")")    #do nothing
                else
                    error("ConstructExpressionTreeError: Invalid n-Tuple detected!");
                end
            else
                push!(queue, strip(String(current_string)));
            end

            push!(queue, ",");

            current_string = Array{Char, 1}([]);
        elseif (character == ' ')   #white space is considered
            if (isOperator)
                push!(queue, strip(String(current_string)));
                current_string = Array{Char, 1}([]);
                isOperator = false;
            end

            push!(current_string, character);
        elseif (character in ('+', '-', '*', '/', '\\', '=', '<', '>', '\$', '|', '%', '^', '~', '&', '?'))
            if (!isOperator)
                if (strip(String(current_string)) != "")
                    push!(queue, strip(String(current_string)));
                end
                current_string = Array{Char, 1}([]);
            end
            push!(current_string, character);
            isOperator = true;
        else    #found new symbol  
            if (isOperator) #first character of new token
                push!(queue, strip(String(current_string)));
                current_string = Array{Char, 1}([]);
                isOperator = false;
            end
            push!(current_string, character);
        end


        if (existing_parenthesis < 0)
            error("ConstructExpressionTreeError: Invalid parentheses syntax detected!");
        end
    end
    #Check for a possible token at the end of the String.
    if (strip(String(current_string)) != "")
        push!(queue, strip(String(current_string)));
    end

    if (existing_parenthesis != 0)
        error("ConstructExpressionTreeError: Invalid number of parentheses!");
    end
    return queue;
end

#Parenthesize any arguments that are not enclosed by parentheses
function parenthesize_arguments(tokens::AbstractVector) 
    local existing_parenthesis::Int64 = 0;
    local comma_indices::Array{Int64, 1} = Array{Int64, 1}([]);
    #keep track of opening and closing parentheses indices
    #keep track of comma indices at the same tree level
    #this function runs after parenthesize_tokens()
    for index in 1:length(tokens)
        if (tokens[index] == ",")
            push!(comma_indices, index);
        end
    end
    for comma_index in reverse(comma_indices)
        ####println("index to modify: ", comma_index, " token: ", tokens[comma_index],
        ####        " comma indices: ", comma_indices, " tokens: ", tokens...);
        no_parentheses = false; #boolean indicating if the current argument is enclosed in parentheses
        #,=>    #the order of indices to search rightward
        existing_parenthesis = 0;
        for index in (comma_index + 1):length(tokens)
            if (tokens[index] == "(")
                existing_parenthesis = existing_parenthesis + 1;
            elseif (tokens[index] == ")")
                existing_parenthesis = existing_parenthesis - 1;
                if (index == (comma_index + 1))
                    error("ConstructExpressionTreeError: Found ')', expected argument!");
                end
            elseif (tokens[index] == ",")
                if (existing_parenthesis == 0)  #found following comma in same tree level
                    #Add parentheses
                    if (no_parentheses)
                        insert!(tokens, index, ")");
                        insert!(tokens, (comma_index + 1), "(");
                    end
                    break;
                end
            else
                if (existing_parenthesis == 0)  #the current argument is not enclosed in parentheses
                    no_parentheses = true;
                end
            end

            if (existing_parenthesis == -1) #found end of arguments for infix function
                ####println("index: ", index, " token: ", tokens[index], " no_parentheses: ", no_parentheses);
                #Add parentheses
                if (no_parentheses)
                    insert!(tokens, index, ")");
                    insert!(tokens, (comma_index + 1), "(");
                end
                break;
            end
        end
        no_parentheses = false; #boolean indicating if the current argument is enclosed in parentheses
        #<=,    #reverse the order of indices to search leftward
        existing_parenthesis = 0;
        for index in reverse(1:(comma_index - 1))
            if (tokens[index] == "(")
                existing_parenthesis = existing_parenthesis + 1;
                if (index == (comma_index - 1))
                    error("ConstructExpressionTreeError: Found '(', expected argument!");
                end
            elseif (tokens[index] == ")")
                existing_parenthesis = existing_parenthesis - 1;
            elseif (tokens[index] == ",")
                if (existing_parenthesis == 0)  #found following comma in same tree level
                    #Add parentheses
                    if (no_parentheses)
                        insert!(tokens, comma_index, ")");
                        insert!(tokens, (index + 1), "(");
                    end
                    break;
                end
            else
                if (existing_parenthesis == 0)  #the current argument is not enclosed in parentheses
                    no_parentheses = true;
                end
            end

            if (existing_parenthesis == 1) #found end of arguments for infix function
                ####println("index: ", index, " token: ", tokens[index], " no_parentheses: ", no_parentheses);
                #Add parentheses
                if (no_parentheses)
                    insert!(tokens, comma_index, ")");
                    insert!(tokens, index, "(");
                end
                break;
            end
        end
    end
    return tokens;
end

function parenthesize_tokens(tokens::AbstractVector)
    local existing_parenthesis::Int64 = 0;
    local add_parentheses_at::Array{Int64, 1} = Array{Int64, 1}([]);   #-1 if nothing should be done
    #Find next prefix operator without a following '('
    for index in 1:length(tokens)
        if (any((function(c::Char)
                        return c in tokens[index];
                    end),
                    ('+', '-', '*', '/', '\\', '=', '<', '>', '\$', '|', '%', '^', '~', '&', '?')))
            #Check if '(' exists already
            if (((index + 1) != length(tokens) + 1) && (tokens[index + 1] != "("))
                push!(add_parentheses_at, index);
            end
        end
    end
    for last_entry_index in reverse(add_parentheses_at)
        ####println("index to modify: ", last_entry_index, " token: ", tokens[last_entry_index],
        ####        " tokens: ", tokens...);
        modified_tokens::Bool = false;
        for index in (last_entry_index + 1):length(tokens)
            if (tokens[index] == "(")
                existing_parenthesis = existing_parenthesis + 1;
            elseif (tokens[index] == ")")
                existing_parenthesis = existing_parenthesis - 1;
            end
            if (existing_parenthesis == 0)
                if (((index + 1) < length(tokens)) &&   #'(' should not exist at the end of the expression
                    (tokens[index + 1] != "("))
                    insert!(tokens, index + 1, ")");
                    insert!(tokens, last_entry_index + 1, "(");
                    modified_tokens = true;
                    break;
                elseif (index == length(tokens))
                    insert!(tokens, index + 1, ")");
                    insert!(tokens, last_entry_index + 1, "(");
                    modified_tokens = true;
                    break;
                end
            elseif (existing_parenthesis == -1) #reached higher tree level (')'), ('(') should exist
                insert!(tokens, index, ")");
                insert!(tokens, last_entry_index + 1, "(");
                existing_parenthesis = 0;
                modified_tokens = true;
                break;
            end
        end
        if (!modified_tokens)
            error("ConstructExpressionTreeError: Could not add parentheses to the expression!");
        end
    end
    return tokens;
end

function construct_expression_tree(tokens::AbstractVector)
    local existing_parenthesis::Int64 = 0;
    local current_node::ExpressionNode = ExpressionNode();
    local root_node::ExpressionNode = current_node;
    local unary_depth::Int64 = 0;   #when operator exists and we traverse to a new child node
    for token in tokens
        if (token == "(")
            existing_parenthesis = existing_parenthesis + 1;

            #Create new level and visit it
            new_node = ExpressionNode(parent=current_node);
            push!(current_node.children, new_node);
            current_node = new_node;
        elseif (token == ")")
            existing_parenthesis = existing_parenthesis - 1;
            if (!isnull(current_node.parent))
                current_node = get(current_node.parent);
            else
                error("ConstructExpressionTreeError: The root node does not have a parent!");
            end
        elseif (token == ",")
            if (!isnull(current_node.value) && get(current_node.value) != ",")
                notFound = true;
                
                new_intermediate_node = ExpressionNode(val=token, parent=get(current_node.parent));
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
                current_node.value = Nullable{String}(",");
            end
        elseif (any((function(c::Char)
                        return c in token;
                    end),
                    ('+', '-', '*', '/', '\\', '=', '<', '>', '\$', '|', '%', '^', '~', '&', '?')))
            ####print("current node: ");
            ####if (!isnull(current_node.value))
            ####    print(get(current_node.value));
            ####else
            ####    print("#NULL");
            ####end
            ####print(" current token: ", token," parent node: ");
            ####if (isnull(current_node.parent))
            ####    print("#NULL");
            ####else
            ####    if (!isnull(get(current_node.parent).value))
            ####        print(get(get(current_node.parent).value));
            ####    else
            ####        print(get(current_node.parent));
            ####    end
            ####end
            ####println();
            ####print("children: ");
            ####for c in current_node.children
            ####    print(get(c.value), ", ");
            ####end
            ####println();
            ####println("operator has ",
            ####        length(current_node.children),
            ####        " arguments!");
            #Check if operator exists already
            if (isnull(current_node.value))
                current_node.value = Nullable{String}(token);
            else
                if (!any((function(c::Char)
                        return c in token;
                    end),
                    ('+', '-', '*', '/', '\\', '=', '<', '>', '\$', '|', '%', '^', '~', '&', '?')))
                    if (isnull(current_node.parent))
                        new_root_node = ExpressionNode(val=token);
                        push!(new_root_node.children, current_node);
                        current_node.parent = new_root_node;
                        current_node = new_root_node;
                    else
                        notFound = true;
                        new_intermediate_node = ExpressionNode(val=token, parent=get(current_node.parent));

                        for (i, c) in enumerate(get(current_node.parent).children)
                            if (c == current_node)
                                deleteat!(get(current_node.parent).children, i);
                                insert!(get(current_node.parent).children, i, new_intermediate_node);
                                notFound = false;
                                break;
                            end
                        end
                        if (notFound)
                            error("ConstructExpressionTreeError: Could not find existing child node!");
                        end

                        current_node.parent = Nullable{ExpressionNode}(new_intermediate_node);
                        push!(new_intermediate_node.children, current_node);
                        current_node = new_intermediate_node;
                    end
                else
                    if (isnull(current_node.parent))
                        new_root_node = ExpressionNode(val=token);
                        current_node.parent = new_root_node;
                        push!(new_root_node.children, current_node);
                        current_node = new_root_node;
                    else
                        notFound = true;
                        new_intermediate_node = ExpressionNode(val=token, parent=get(current_node.parent));

                        for (i, c) in enumerate(get(current_node.parent).children)
                            if (c == current_node)
                                deleteat!(get(current_node.parent).children, i);
                                insert!(get(current_node.parent).children, i, new_intermediate_node);
                                notFound = false;
                                break;
                            end
                        end
                        if (notFound)
                            error("ConstructExpressionTreeError: Could not find existing child node!");
                        end

                        current_node.parent = Nullable{ExpressionNode}(new_intermediate_node);
                        push!(new_intermediate_node.children, current_node);
                        current_node = new_intermediate_node;
                    end
                end
            end
        else    #Not a special operator
            if (isnull(current_node.value))
                current_node.value = Nullable{String}(token);
            else
                new_node = ExpressionNode(val=token, parent=current_node);
                push!(current_node.children, new_node);
            end
        end


        if (existing_parenthesis < 0)
            error("ConstructExpressionTreeError: Invalid parentheses syntax detected!");
        end
    end

    while (!isnull(root_node.parent))
        root_node = get(root_node.parent);
    end

    if (existing_parenthesis != 0)
        error("ConstructExpressionTreeError: Invalid number of parentheses!");
    end
    return root_node;
end

function prune_nodes(node::ExpressionNode)
    #remove valueless nodes that have 1 child
    for child in node.children
        prune_nodes(child);
    end
    if (isnull(node.value))
        if (length(node.children) == 1)
            if (isnull(node.parent))
                new_root_node = pop!(node.children);
                new_root_node.parent = Nullable{ExpressionNode}();
                return new_root_node;
            else
                notFound = true;
                new_node = pop!(node.children);

                for (i, c) in enumerate(get(node.parent).children)
                    if (c == node)
                        deleteat!(get(current_node.parent).children, i);
                        insert!(get(current_node.parent).children, i, new_node);
                        notFound = false;
                        break;
                    end
                end
                if (notFound)
                    error("ConstructExpressionTreeError: Could not find existing child node!");
                end

                new_node.parent = Nullable{ExpressionNode}(current_node.parent);
                return new_node;
            end
        else
            error("ConstructExpressionTreeError: Found ", length(node.children), " children in valueless ExpressionNode!");
        end
    end
    return node;
end

function parse_expression(s::String)
    local tokens::AbstractVector = identify_tokens(s);
    tokens = parenthesize_tokens(tokens);
    tokens = parenthesize_arguments(tokens);
    local root_node::ExpressionNode = construct_expression_tree(tokens);
    root_node = prune_nodes(root_node);
    return evaluate_expression_tree(root_node);
end

#Some special cases for parse_expression()

#parse_expression("P ==> (Q(1))");

#parse_expression("P ==> (Q(1, 2))");

#parse_expression("Q(P(x) ==> A, S(x)) ==> R(x)");

#parse_expression("F(x, x) & G(x, y) & H(y, z) & R(A, z, z)");

#parse_expression("P & Q | ~R(x, F(x))");

function evaluate_expression_tree(node::ExpressionNode)
    local queue::AbstractVector = [];
    for child in node.children
        if (get(child.value) != ",")
            push!(queue, evaluate_expression_tree(child));
        else #Use current operator for childrens' children
            for child_child in child.children
                push!(queue, evaluate_expression_tree(child_child));
            end
        end
    end
    if (length(node.children) == 0)
        return Expression(get(node.value));
    else
        return Expression(get(node.value), queue...);
    end
end

