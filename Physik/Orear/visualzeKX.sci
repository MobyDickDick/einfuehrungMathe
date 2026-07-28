function fx = f(x)
    d = 3
    fx = sqrt(1-d/sqrt(d^2+x^2))
endfunction

x = linspace(0,200,1000);

plot(x, f)
