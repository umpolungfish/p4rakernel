import os

# Define the folder path (use '.' for the current folder)
folder_path = '.' 

target_text = """"""

for root, dirs, files in os.walk(folder_path):
    for file in files:
        # Skip the script itself if placed in the same folder
        if file == 'cleanup.py':
            continue
            
        file_path = os.path.join(root, file)
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            if target_text in content:
                updated_content = content.replace(target_text, '')
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(updated_content)
                print(f"Cleaned: {file_path}")
        except Exception as e:
            # Skips binary or unreadable files safely
            continue