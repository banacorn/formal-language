command! WC w<bar>call system("echo ".expand('%')." | nc localhost 1531")
imap <C-g> <ESC>:WC<CR>
nmap <C-g> <ESC>:WC<CR>

nmap <C-c> :call Wrap_comment()<CR>
vmap <C-c> :call Wrap_comment()<CR>

function! Wrap_comment ()
    let l:line = getline('.')

    let l:prefix_space = matchstr(l:line, '^ *')
    let l:after_space_data = l:line[strlen(l:prefix_space):]

    if l:after_space_data[0:1] == '--'
        let l:after_space_data = l:after_space_data[2:]

    else
        let l:after_space_data = '--' . l:after_space_data
    endif

    call setline('.', l:prefix_space . l:after_space_data)
    execute "normal ^l"
    echom ""
endfunction
